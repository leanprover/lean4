// Lean compiler output
// Module: Lean.DocString.Add
// Imports: import Lean.Elab.DocString public import Lean.DocString.Parser public import Lean.Elab.Term.TermElabM
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_document(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_block(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_exec___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_doc_verso;
lean_object* l_Lean_findInternalDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_removeBuiltinDocString(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__5___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Documentation comment has no source location, cannot parse"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__11___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__11___closed__0_value;
static lean_once_cell_t l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_parseVersoDocString___redArg___lam__11___closed__1;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__1_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__2 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__2_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__3 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__3_value;
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_parseVersoDocString___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__4 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__4_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_parseVersoDocString___redArg___closed__5 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6_value;
static const lean_string_object l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7 = (const lean_object*)&l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static const lean_ctor_object l_Lean_versoDocString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__0_value),((lean_object*)&l_Lean_versoDocString___closed__0_value)}};
static const lean_object* l_Lean_versoDocString___closed__1 = (const lean_object*)&l_Lean_versoDocString___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringFromString___closed__0 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__0_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringFromString___closed__1 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__1_value;
static const lean_closure_object l_Lean_versoDocStringFromString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_versoDocStringFromString___closed__1_value)} };
static const lean_object* l_Lean_versoDocStringFromString___closed__2 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__2_value;
static const lean_array_object l_Lean_versoDocStringFromString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringFromString___closed__3 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__3_value;
static const lean_string_object l_Lean_versoDocStringFromString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_versoDocStringFromString___closed__4 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__4_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__5 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__5_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__5_value),((lean_object*)&l_Lean_versoDocStringFromString___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__6 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration `"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is in an imported module"};
static const lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_addMarkdownDocString___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration '"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is in an imported module"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Error adding module docs: "};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "Can't add Verso-format module docs because there is already Markdown-format content present."};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "invalid doc string removal, declaration `"};
static const lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0 = (const lean_object*)&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_makeDocStringVerso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Documentation for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__0 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__0_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__1;
static const lean_string_object l_Lean_makeDocStringVerso___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already in Verso format"};
static const lean_object* l_Lean_makeDocStringVerso___closed__2 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__2_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__3;
static const lean_string_object l_Lean_makeDocStringVerso___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "No documentation found for `"};
static const lean_object* l_Lean_makeDocStringVerso___closed__4 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__4_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__5;
static const lean_string_object l_Lean_makeDocStringVerso___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_makeDocStringVerso___closed__6 = (const lean_object*)&l_Lean_makeDocStringVerso___closed__6_value;
static lean_once_cell_t l_Lean_makeDocStringVerso___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_makeDocStringVerso___closed__7;
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____s_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object* v___x_5_, lean_object* v_toPure_6_, lean_object* v_r_7_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_5_);
v___x_9_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object* v___y_10_, lean_object* v_str_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_toBind_16_, lean_object* v___f_17_, lean_object* v___f_18_, lean_object* v_a_19_, lean_object* v_x_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_fst_22_; 
v_fst_22_ = lean_ctor_get(v_a_19_, 0);
lean_inc(v_fst_22_);
if (lean_obj_tag(v___y_10_) == 1)
{
lean_object* v_snd_23_; lean_object* v_start_24_; lean_object* v_stop_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_48_; 
lean_dec(v___f_18_);
v_snd_23_ = lean_ctor_get(v_a_19_, 1);
lean_inc(v_snd_23_);
lean_dec_ref(v_a_19_);
v_start_24_ = lean_ctor_get(v_fst_22_, 0);
v_stop_25_ = lean_ctor_get(v_fst_22_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_fst_22_);
if (v_isSharedCheck_48_ == 0)
{
v___x_27_ = v_fst_22_;
v_isShared_28_ = v_isSharedCheck_48_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_stop_25_);
lean_inc(v_start_24_);
lean_dec(v_fst_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_48_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_47_; 
v_val_29_ = lean_ctor_get(v___y_10_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___y_10_);
if (v_isSharedCheck_47_ == 0)
{
v___x_31_ = v___y_10_;
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v___y_10_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_33_ = lean_nat_add(v_val_29_, v_start_24_);
v___x_34_ = lean_nat_add(v_val_29_, v_stop_25_);
lean_dec(v_val_29_);
v___x_35_ = 0;
v___x_36_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_36_, 0, v___x_33_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*2, v___x_35_);
v___x_37_ = lean_string_utf8_extract(v_str_11_, v_start_24_, v_stop_25_);
lean_dec(v_stop_25_);
lean_dec(v_start_24_);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 2);
lean_ctor_set(v___x_27_, 1, v___x_37_);
lean_ctor_set(v___x_27_, 0, v___x_36_);
v___x_39_ = v___x_27_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_46_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_41_; 
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 3);
lean_ctor_set(v___x_31_, 0, v_snd_23_);
v___x_41_ = v___x_31_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_snd_23_);
v___x_41_ = v_reuseFailAlloc_45_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = l_Lean_MessageData_ofFormat(v___x_41_);
v___x_43_ = l_Lean_logErrorAt___redArg(v_inst_12_, v_inst_13_, v_inst_14_, v_inst_15_, v___x_39_, v___x_42_);
v___x_44_ = lean_apply_4(v_toBind_16_, lean_box(0), lean_box(0), v___x_43_, v___f_17_);
return v___x_44_;
}
}
}
}
}
else
{
lean_object* v_snd_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v_fst_22_);
lean_dec(v___f_17_);
lean_dec(v___y_10_);
v_snd_49_ = lean_ctor_get(v_a_19_, 1);
lean_inc(v_snd_49_);
lean_dec_ref(v_a_19_);
v___x_50_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_50_, 0, v_snd_49_);
v___x_51_ = l_Lean_MessageData_ofFormat(v___x_50_);
v___x_52_ = l_Lean_logError___redArg(v_inst_12_, v_inst_13_, v_inst_14_, v_inst_15_, v___x_51_);
v___x_53_ = lean_apply_4(v_toBind_16_, lean_box(0), lean_box(0), v___x_52_, v___f_18_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object* v___y_54_, lean_object* v_str_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_toBind_60_, lean_object* v___f_61_, lean_object* v___f_62_, lean_object* v_a_63_, lean_object* v_x_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_validateDocComment___redArg___lam__3(v___y_54_, v_str_55_, v_inst_56_, v_inst_57_, v_inst_58_, v_inst_59_, v_toBind_60_, v___f_61_, v___f_62_, v_a_63_, v_x_64_, v___y_65_);
lean_dec_ref(v_str_55_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object* v_toPure_67_, lean_object* v___y_68_, lean_object* v_str_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_, lean_object* v_toBind_74_, lean_object* v___f_75_, lean_object* v_____x_76_){
_start:
{
lean_object* v_fst_77_; lean_object* v___x_78_; lean_object* v___f_79_; lean_object* v___f_80_; size_t v_sz_81_; size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_fst_77_ = lean_ctor_get(v_____x_76_, 0);
lean_inc(v_fst_77_);
lean_dec_ref(v_____x_76_);
v___x_78_ = lean_box(0);
v___f_79_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__1), 3, 2);
lean_closure_set(v___f_79_, 0, v___x_78_);
lean_closure_set(v___f_79_, 1, v_toPure_67_);
lean_inc_ref(v___f_79_);
lean_inc(v_toBind_74_);
lean_inc_ref(v_inst_70_);
v___f_80_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__3___boxed), 12, 9);
lean_closure_set(v___f_80_, 0, v___y_68_);
lean_closure_set(v___f_80_, 1, v_str_69_);
lean_closure_set(v___f_80_, 2, v_inst_70_);
lean_closure_set(v___f_80_, 3, v_inst_71_);
lean_closure_set(v___f_80_, 4, v_inst_72_);
lean_closure_set(v___f_80_, 5, v_inst_73_);
lean_closure_set(v___f_80_, 6, v_toBind_74_);
lean_closure_set(v___f_80_, 7, v___f_79_);
lean_closure_set(v___f_80_, 8, v___f_79_);
v_sz_81_ = lean_array_size(v_fst_77_);
v___x_82_ = ((size_t)0ULL);
v___x_83_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_70_, v_fst_77_, v___f_80_, v_sz_81_, v___x_82_, v___x_78_);
v___x_84_ = lean_apply_4(v_toBind_74_, lean_box(0), lean_box(0), v___x_83_, v___f_75_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_docstring_90_){
_start:
{
lean_object* v_toApplicative_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v_str_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___y_100_; 
v_toApplicative_91_ = lean_ctor_get(v_inst_85_, 0);
v_toBind_92_ = lean_ctor_get(v_inst_85_, 1);
lean_inc(v_toBind_92_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc_n(v_toPure_93_, 2);
v_str_94_ = l_Lean_TSyntax_getDocString(v_docstring_90_);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = l_Lean_Syntax_getArg(v_docstring_90_, v___x_95_);
v___x_97_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_96_);
lean_dec(v___x_96_);
v___f_98_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_98_, 0, v_toPure_93_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v___x_106_; 
v___x_106_ = lean_box(0);
v___y_100_ = v___x_106_;
goto v___jp_99_;
}
else
{
lean_object* v_val_107_; uint8_t v___x_108_; lean_object* v___x_109_; 
v_val_107_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_107_);
lean_dec_ref(v___x_97_);
v___x_108_ = 0;
v___x_109_ = l_Lean_SourceInfo_getPos_x3f(v_val_107_, v___x_108_);
lean_dec(v_val_107_);
v___y_100_ = v___x_109_;
goto v___jp_99_;
}
v___jp_99_:
{
lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
lean_inc(v_toBind_92_);
lean_inc_ref(v_str_94_);
v___f_101_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__2), 10, 9);
lean_closure_set(v___f_101_, 0, v_toPure_93_);
lean_closure_set(v___f_101_, 1, v___y_100_);
lean_closure_set(v___f_101_, 2, v_str_94_);
lean_closure_set(v___f_101_, 3, v_inst_85_);
lean_closure_set(v___f_101_, 4, v_inst_87_);
lean_closure_set(v___f_101_, 5, v_inst_88_);
lean_closure_set(v___f_101_, 6, v_inst_89_);
lean_closure_set(v___f_101_, 7, v_toBind_92_);
lean_closure_set(v___f_101_, 8, v___f_98_);
v___x_102_ = l_Lean_rewriteManualLinksCore(v_str_94_);
v___x_103_ = lean_alloc_closure((void*)(l_instMonadEIO___aux__5___boxed), 4, 3);
lean_closure_set(v___x_103_, 0, lean_box(0));
lean_closure_set(v___x_103_, 1, lean_box(0));
lean_closure_set(v___x_103_, 2, v___x_102_);
v___x_104_ = lean_apply_2(v_inst_86_, lean_box(0), v___x_103_);
v___x_105_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_104_, v___f_101_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_docstring_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_validateDocComment___redArg(v_inst_110_, v_inst_111_, v_inst_112_, v_inst_113_, v_inst_114_, v_docstring_115_);
lean_dec(v_docstring_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* v_m_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_docstring_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_validateDocComment___redArg(v_inst_118_, v_inst_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_docstring_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_docstring_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_validateDocComment(v_m_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_, v_inst_130_, v_docstring_131_);
lean_dec(v_docstring_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* v_toApplicative_133_, lean_object* v_____s_134_){
_start:
{
lean_object* v_toPure_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_toPure_135_ = lean_ctor_get(v_toApplicative_133_, 1);
lean_inc(v_toPure_135_);
lean_dec_ref(v_toApplicative_133_);
v___x_136_ = lean_box(0);
v___x_137_ = lean_apply_2(v_toPure_135_, lean_box(0), v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* v_toApplicative_138_, lean_object* v_____r_139_){
_start:
{
lean_object* v_toPure_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_toPure_140_ = lean_ctor_get(v_toApplicative_138_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_138_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_2(v_toPure_140_, lean_box(0), v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v_toApplicative_143_, lean_object* v___x_144_, lean_object* v_____r_145_){
_start:
{
lean_object* v_toPure_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_toPure_146_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_146_);
lean_dec_ref(v_toApplicative_143_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_144_);
v___x_148_ = lean_apply_2(v_toPure_146_, lean_box(0), v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_text_150_, lean_object* v_fst_151_, lean_object* v_snd_152_, uint8_t v___x_153_, lean_object* v_logMessage_154_, lean_object* v_toBind_155_, lean_object* v___f_156_, lean_object* v_____do__lift_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_158_ = l_Lean_FileMap_toPosition(v_text_150_, v_fst_151_);
v___x_159_ = lean_box(0);
v___x_160_ = 2;
v___x_161_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_162_ = l_Lean_Parser_Error_toString(v_snd_152_);
v___x_163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___x_164_ = l_Lean_MessageData_ofFormat(v___x_163_);
v___x_165_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_165_, 0, v_____do__lift_157_);
lean_ctor_set(v___x_165_, 1, v___x_158_);
lean_ctor_set(v___x_165_, 2, v___x_159_);
lean_ctor_set(v___x_165_, 3, v___x_161_);
lean_ctor_set(v___x_165_, 4, v___x_164_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5, v___x_153_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 1, v___x_160_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 2, v___x_153_);
v___x_166_ = lean_apply_1(v_logMessage_154_, v___x_165_);
v___x_167_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_166_, v___f_156_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object* v_text_168_, lean_object* v_fst_169_, lean_object* v_snd_170_, lean_object* v___x_171_, lean_object* v_logMessage_172_, lean_object* v_toBind_173_, lean_object* v___f_174_, lean_object* v_____do__lift_175_){
_start:
{
uint8_t v___x_1932__boxed_176_; lean_object* v_res_177_; 
v___x_1932__boxed_176_ = lean_unbox(v___x_171_);
v_res_177_ = l_Lean_parseVersoDocString___redArg___lam__3(v_text_168_, v_fst_169_, v_snd_170_, v___x_1932__boxed_176_, v_logMessage_172_, v_toBind_173_, v___f_174_, v_____do__lift_175_);
lean_dec(v_fst_169_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_178_, uint8_t v___x_179_, lean_object* v_logMessage_180_, lean_object* v_toBind_181_, lean_object* v___f_182_, lean_object* v_getFileName_183_, lean_object* v_a_184_, lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_snd_187_; lean_object* v_fst_188_; lean_object* v_snd_189_; lean_object* v___x_190_; lean_object* v___f_191_; lean_object* v___x_192_; 
v_snd_187_ = lean_ctor_get(v_a_184_, 1);
lean_inc(v_snd_187_);
v_fst_188_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_fst_188_);
lean_dec_ref(v_a_184_);
v_snd_189_ = lean_ctor_get(v_snd_187_, 1);
lean_inc(v_snd_189_);
lean_dec(v_snd_187_);
v___x_190_ = lean_box(v___x_179_);
lean_inc(v_toBind_181_);
v___f_191_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_191_, 0, v_text_178_);
lean_closure_set(v___f_191_, 1, v_fst_188_);
lean_closure_set(v___f_191_, 2, v_snd_189_);
lean_closure_set(v___f_191_, 3, v___x_190_);
lean_closure_set(v___f_191_, 4, v_logMessage_180_);
lean_closure_set(v___f_191_, 5, v_toBind_181_);
lean_closure_set(v___f_191_, 6, v___f_182_);
v___x_192_ = lean_apply_4(v_toBind_181_, lean_box(0), lean_box(0), v_getFileName_183_, v___f_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_193_, lean_object* v___x_194_, lean_object* v_logMessage_195_, lean_object* v_toBind_196_, lean_object* v___f_197_, lean_object* v_getFileName_198_, lean_object* v_a_199_, lean_object* v_x_200_, lean_object* v___y_201_){
_start:
{
uint8_t v___x_1966__boxed_202_; lean_object* v_res_203_; 
v___x_1966__boxed_202_ = lean_unbox(v___x_194_);
v_res_203_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_193_, v___x_1966__boxed_202_, v_logMessage_195_, v_toBind_196_, v___f_197_, v_getFileName_198_, v_a_199_, v_x_200_, v___y_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_text_206_, lean_object* v_pos_207_, lean_object* v_source_208_, uint8_t v___x_209_, lean_object* v_logMessage_210_, lean_object* v_toBind_211_, lean_object* v___f_212_, lean_object* v_____do__lift_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint32_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_214_ = l_Lean_FileMap_toPosition(v_text_206_, v_pos_207_);
v___x_215_ = lean_box(0);
v___x_216_ = 2;
v___x_217_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_218_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_219_ = lean_string_utf8_get(v_source_208_, v_pos_207_);
v___x_220_ = lean_string_push(v___x_217_, v___x_219_);
v___x_221_ = lean_string_append(v___x_218_, v___x_220_);
lean_dec_ref(v___x_220_);
v___x_222_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_223_ = lean_string_append(v___x_221_, v___x_222_);
v___x_224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
v___x_225_ = l_Lean_MessageData_ofFormat(v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_226_, 0, v_____do__lift_213_);
lean_ctor_set(v___x_226_, 1, v___x_214_);
lean_ctor_set(v___x_226_, 2, v___x_215_);
lean_ctor_set(v___x_226_, 3, v___x_217_);
lean_ctor_set(v___x_226_, 4, v___x_225_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5, v___x_209_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5 + 1, v___x_216_);
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*5 + 2, v___x_209_);
v___x_227_ = lean_apply_1(v_logMessage_210_, v___x_226_);
v___x_228_ = lean_apply_4(v_toBind_211_, lean_box(0), lean_box(0), v___x_227_, v___f_212_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object* v_text_229_, lean_object* v_pos_230_, lean_object* v_source_231_, lean_object* v___x_232_, lean_object* v_logMessage_233_, lean_object* v_toBind_234_, lean_object* v___f_235_, lean_object* v_____do__lift_236_){
_start:
{
uint8_t v___x_1996__boxed_237_; lean_object* v_res_238_; 
v___x_1996__boxed_237_ = lean_unbox(v___x_232_);
v_res_238_ = l_Lean_parseVersoDocString___redArg___lam__5(v_text_229_, v_pos_230_, v_source_231_, v___x_1996__boxed_237_, v_logMessage_233_, v_toBind_234_, v___f_235_, v_____do__lift_236_);
lean_dec_ref(v_source_231_);
lean_dec(v_pos_230_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_toApplicative_239_, lean_object* v_text_240_, lean_object* v_logMessage_241_, lean_object* v_toBind_242_, lean_object* v_getFileName_243_, lean_object* v_inst_244_, lean_object* v___f_245_, lean_object* v_ictx_246_, lean_object* v_source_247_, lean_object* v___f_248_, lean_object* v_env_249_, lean_object* v_____do__lift_250_, lean_object* v_____do__lift_251_, lean_object* v_val_252_, lean_object* v___y_253_, lean_object* v___x_254_, lean_object* v_____do__lift_255_){
_start:
{
lean_object* v___y_257_; lean_object* v_pmctx_280_; lean_object* v_blockCtxt_281_; lean_object* v___x_282_; lean_object* v_s_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_s_286_; uint8_t v___y_288_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
lean_inc_ref(v_env_249_);
v_pmctx_280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_280_, 0, v_env_249_);
lean_ctor_set(v_pmctx_280_, 1, v_____do__lift_250_);
lean_ctor_set(v_pmctx_280_, 2, v_____do__lift_251_);
lean_ctor_set(v_pmctx_280_, 3, v_____do__lift_255_);
lean_inc(v_val_252_);
lean_inc_ref(v_text_240_);
v_blockCtxt_281_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_240_, v_val_252_, v___y_253_);
v___x_282_ = l_Lean_Parser_mkParserState(v_source_247_);
lean_inc_ref(v___x_282_);
v_s_283_ = l_Lean_Parser_ParserState_setPos(v___x_282_, v_val_252_);
v___x_284_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_284_, 0, v_blockCtxt_281_);
v___x_285_ = l_Lean_Parser_getTokenTable(v_env_249_);
lean_inc_ref(v___x_285_);
lean_inc_ref(v_pmctx_280_);
lean_inc_ref(v_ictx_246_);
v_s_286_ = l_Lean_Parser_ParserFn_run(v___x_284_, v_ictx_246_, v_pmctx_280_, v___x_285_, v_s_283_);
lean_inc_ref(v_s_286_);
v___x_298_ = l_Lean_Parser_ParserState_allErrors(v_s_286_);
v___x_299_ = lean_array_get_size(v___x_298_);
lean_dec_ref(v___x_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
v___y_288_ = v___x_301_;
goto v___jp_287_;
}
else
{
lean_object* v_pos_302_; uint8_t v___x_303_; 
v_pos_302_ = lean_ctor_get(v_s_286_, 2);
lean_inc(v_pos_302_);
v___x_303_ = l_Lean_Parser_InputContext_atEnd(v_ictx_246_, v_pos_302_);
lean_dec(v_pos_302_);
if (v___x_303_ == 0)
{
v___y_288_ = v___x_301_;
goto v___jp_287_;
}
else
{
lean_dec_ref(v___x_285_);
lean_dec_ref(v___x_282_);
lean_dec_ref(v_pmctx_280_);
lean_dec(v___x_254_);
v___y_257_ = v_s_286_;
goto v___jp_256_;
}
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
lean_inc_ref(v___y_257_);
v___x_258_ = l_Lean_Parser_ParserState_allErrors(v___y_257_);
v___x_259_ = lean_array_get_size(v___x_258_);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_nat_dec_eq(v___x_259_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___f_265_; size_t v_sz_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v___y_257_);
lean_dec(v___f_248_);
lean_dec_ref(v_source_247_);
lean_dec_ref(v_ictx_246_);
v___x_262_ = lean_box(0);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_263_, 0, v_toApplicative_239_);
lean_closure_set(v___f_263_, 1, v___x_262_);
v___x_264_ = lean_box(v___x_261_);
lean_inc(v_toBind_242_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_265_, 0, v_text_240_);
lean_closure_set(v___f_265_, 1, v___x_264_);
lean_closure_set(v___f_265_, 2, v_logMessage_241_);
lean_closure_set(v___f_265_, 3, v_toBind_242_);
lean_closure_set(v___f_265_, 4, v___f_263_);
lean_closure_set(v___f_265_, 5, v_getFileName_243_);
v_sz_266_ = lean_array_size(v___x_258_);
v___x_267_ = ((size_t)0ULL);
v___x_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_244_, v___x_258_, v___f_265_, v_sz_266_, v___x_267_, v___x_262_);
v___x_269_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_268_, v___f_245_);
return v___x_269_;
}
else
{
lean_object* v_stxStack_270_; lean_object* v_pos_271_; uint8_t v___x_272_; 
lean_dec_ref(v___x_258_);
lean_dec(v___f_245_);
lean_dec_ref(v_inst_244_);
v_stxStack_270_ = lean_ctor_get(v___y_257_, 0);
lean_inc_ref(v_stxStack_270_);
v_pos_271_ = lean_ctor_get(v___y_257_, 2);
lean_inc(v_pos_271_);
lean_dec_ref(v___y_257_);
v___x_272_ = l_Lean_Parser_InputContext_atEnd(v_ictx_246_, v_pos_271_);
lean_dec_ref(v_ictx_246_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
lean_dec_ref(v_stxStack_270_);
lean_dec_ref(v_toApplicative_239_);
v___x_273_ = lean_box(v___x_272_);
lean_inc(v_toBind_242_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_274_, 0, v_text_240_);
lean_closure_set(v___f_274_, 1, v_pos_271_);
lean_closure_set(v___f_274_, 2, v_source_247_);
lean_closure_set(v___f_274_, 3, v___x_273_);
lean_closure_set(v___f_274_, 4, v_logMessage_241_);
lean_closure_set(v___f_274_, 5, v_toBind_242_);
lean_closure_set(v___f_274_, 6, v___f_248_);
v___x_275_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v_getFileName_243_, v___f_274_);
return v___x_275_;
}
else
{
lean_object* v_toPure_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_pos_271_);
lean_dec(v___f_248_);
lean_dec_ref(v_source_247_);
lean_dec(v_getFileName_243_);
lean_dec(v_toBind_242_);
lean_dec(v_logMessage_241_);
lean_dec_ref(v_text_240_);
v_toPure_276_ = lean_ctor_get(v_toApplicative_239_, 1);
lean_inc(v_toPure_276_);
lean_dec_ref(v_toApplicative_239_);
v___x_277_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_270_);
lean_dec_ref(v_stxStack_270_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
v___x_279_ = lean_apply_2(v_toPure_276_, lean_box(0), v___x_278_);
return v___x_279_;
}
}
}
v___jp_287_:
{
if (v___y_288_ == 0)
{
lean_dec_ref(v___x_285_);
lean_dec_ref(v___x_282_);
lean_dec_ref(v_pmctx_280_);
lean_dec(v___x_254_);
v___y_257_ = v_s_286_;
goto v___jp_256_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v_pos_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_box(0);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_254_);
lean_ctor_set(v___x_292_, 1, v___x_289_);
v___x_293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_293_, 0, v___x_289_);
lean_ctor_set(v___x_293_, 1, v___x_290_);
lean_ctor_set(v___x_293_, 2, v___x_291_);
lean_ctor_set(v___x_293_, 3, v___x_292_);
lean_ctor_set(v___x_293_, 4, v___x_289_);
v_pos_294_ = lean_ctor_get(v_s_286_, 2);
lean_inc(v_pos_294_);
lean_dec_ref(v_s_286_);
v___x_295_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_295_, 0, v___x_293_);
v___x_296_ = l_Lean_Parser_ParserState_setPos(v___x_282_, v_pos_294_);
lean_inc_ref(v_ictx_246_);
v___x_297_ = l_Lean_Parser_ParserFn_run(v___x_295_, v_ictx_246_, v_pmctx_280_, v___x_285_, v___x_296_);
v___y_257_ = v___x_297_;
goto v___jp_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_toApplicative_304_ = _args[0];
lean_object* v_text_305_ = _args[1];
lean_object* v_logMessage_306_ = _args[2];
lean_object* v_toBind_307_ = _args[3];
lean_object* v_getFileName_308_ = _args[4];
lean_object* v_inst_309_ = _args[5];
lean_object* v___f_310_ = _args[6];
lean_object* v_ictx_311_ = _args[7];
lean_object* v_source_312_ = _args[8];
lean_object* v___f_313_ = _args[9];
lean_object* v_env_314_ = _args[10];
lean_object* v_____do__lift_315_ = _args[11];
lean_object* v_____do__lift_316_ = _args[12];
lean_object* v_val_317_ = _args[13];
lean_object* v___y_318_ = _args[14];
lean_object* v___x_319_ = _args[15];
lean_object* v_____do__lift_320_ = _args[16];
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_parseVersoDocString___redArg___lam__6(v_toApplicative_304_, v_text_305_, v_logMessage_306_, v_toBind_307_, v_getFileName_308_, v_inst_309_, v___f_310_, v_ictx_311_, v_source_312_, v___f_313_, v_env_314_, v_____do__lift_315_, v_____do__lift_316_, v_val_317_, v___y_318_, v___x_319_, v_____do__lift_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_toApplicative_322_, lean_object* v_text_323_, lean_object* v_logMessage_324_, lean_object* v_toBind_325_, lean_object* v_getFileName_326_, lean_object* v_inst_327_, lean_object* v___f_328_, lean_object* v_ictx_329_, lean_object* v_source_330_, lean_object* v___f_331_, lean_object* v_env_332_, lean_object* v_____do__lift_333_, lean_object* v_val_334_, lean_object* v___y_335_, lean_object* v___x_336_, lean_object* v_getOpenDecls_337_, lean_object* v_____do__lift_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; 
lean_inc(v_toBind_325_);
v___f_339_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_339_, 0, v_toApplicative_322_);
lean_closure_set(v___f_339_, 1, v_text_323_);
lean_closure_set(v___f_339_, 2, v_logMessage_324_);
lean_closure_set(v___f_339_, 3, v_toBind_325_);
lean_closure_set(v___f_339_, 4, v_getFileName_326_);
lean_closure_set(v___f_339_, 5, v_inst_327_);
lean_closure_set(v___f_339_, 6, v___f_328_);
lean_closure_set(v___f_339_, 7, v_ictx_329_);
lean_closure_set(v___f_339_, 8, v_source_330_);
lean_closure_set(v___f_339_, 9, v___f_331_);
lean_closure_set(v___f_339_, 10, v_env_332_);
lean_closure_set(v___f_339_, 11, v_____do__lift_333_);
lean_closure_set(v___f_339_, 12, v_____do__lift_338_);
lean_closure_set(v___f_339_, 13, v_val_334_);
lean_closure_set(v___f_339_, 14, v___y_335_);
lean_closure_set(v___f_339_, 15, v___x_336_);
v___x_340_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v_getOpenDecls_337_, v___f_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_toApplicative_341_ = _args[0];
lean_object* v_text_342_ = _args[1];
lean_object* v_logMessage_343_ = _args[2];
lean_object* v_toBind_344_ = _args[3];
lean_object* v_getFileName_345_ = _args[4];
lean_object* v_inst_346_ = _args[5];
lean_object* v___f_347_ = _args[6];
lean_object* v_ictx_348_ = _args[7];
lean_object* v_source_349_ = _args[8];
lean_object* v___f_350_ = _args[9];
lean_object* v_env_351_ = _args[10];
lean_object* v_____do__lift_352_ = _args[11];
lean_object* v_val_353_ = _args[12];
lean_object* v___y_354_ = _args[13];
lean_object* v___x_355_ = _args[14];
lean_object* v_getOpenDecls_356_ = _args[15];
lean_object* v_____do__lift_357_ = _args[16];
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_parseVersoDocString___redArg___lam__7(v_toApplicative_341_, v_text_342_, v_logMessage_343_, v_toBind_344_, v_getFileName_345_, v_inst_346_, v___f_347_, v_ictx_348_, v_source_349_, v___f_350_, v_env_351_, v_____do__lift_352_, v_val_353_, v___y_354_, v___x_355_, v_getOpenDecls_356_, v_____do__lift_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_inst_359_, lean_object* v_toApplicative_360_, lean_object* v_text_361_, lean_object* v_logMessage_362_, lean_object* v_toBind_363_, lean_object* v_getFileName_364_, lean_object* v_inst_365_, lean_object* v___f_366_, lean_object* v_ictx_367_, lean_object* v_source_368_, lean_object* v___f_369_, lean_object* v_env_370_, lean_object* v_val_371_, lean_object* v___y_372_, lean_object* v___x_373_, lean_object* v_____do__lift_374_){
_start:
{
lean_object* v_getCurrNamespace_375_; lean_object* v_getOpenDecls_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v_getCurrNamespace_375_ = lean_ctor_get(v_inst_359_, 0);
lean_inc(v_getCurrNamespace_375_);
v_getOpenDecls_376_ = lean_ctor_get(v_inst_359_, 1);
lean_inc(v_getOpenDecls_376_);
lean_dec_ref(v_inst_359_);
lean_inc(v_toBind_363_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_377_, 0, v_toApplicative_360_);
lean_closure_set(v___f_377_, 1, v_text_361_);
lean_closure_set(v___f_377_, 2, v_logMessage_362_);
lean_closure_set(v___f_377_, 3, v_toBind_363_);
lean_closure_set(v___f_377_, 4, v_getFileName_364_);
lean_closure_set(v___f_377_, 5, v_inst_365_);
lean_closure_set(v___f_377_, 6, v___f_366_);
lean_closure_set(v___f_377_, 7, v_ictx_367_);
lean_closure_set(v___f_377_, 8, v_source_368_);
lean_closure_set(v___f_377_, 9, v___f_369_);
lean_closure_set(v___f_377_, 10, v_env_370_);
lean_closure_set(v___f_377_, 11, v_____do__lift_374_);
lean_closure_set(v___f_377_, 12, v_val_371_);
lean_closure_set(v___f_377_, 13, v___y_372_);
lean_closure_set(v___f_377_, 14, v___x_373_);
lean_closure_set(v___f_377_, 15, v_getOpenDecls_376_);
v___x_378_ = lean_apply_4(v_toBind_363_, lean_box(0), lean_box(0), v_getCurrNamespace_375_, v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_source_379_, lean_object* v_text_380_, lean_object* v___y_381_, lean_object* v_inst_382_, lean_object* v_toApplicative_383_, lean_object* v_logMessage_384_, lean_object* v_toBind_385_, lean_object* v_getFileName_386_, lean_object* v_inst_387_, lean_object* v___f_388_, lean_object* v___f_389_, lean_object* v_env_390_, lean_object* v_val_391_, lean_object* v___x_392_, lean_object* v_inst_393_, lean_object* v_____do__lift_394_){
_start:
{
lean_object* v_ictx_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
lean_inc(v___y_381_);
lean_inc_ref(v_text_380_);
lean_inc_ref(v_source_379_);
v_ictx_395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_395_, 0, v_source_379_);
lean_ctor_set(v_ictx_395_, 1, v_____do__lift_394_);
lean_ctor_set(v_ictx_395_, 2, v_text_380_);
lean_ctor_set(v_ictx_395_, 3, v___y_381_);
lean_inc(v_toBind_385_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(v___f_396_, 0, v_inst_382_);
lean_closure_set(v___f_396_, 1, v_toApplicative_383_);
lean_closure_set(v___f_396_, 2, v_text_380_);
lean_closure_set(v___f_396_, 3, v_logMessage_384_);
lean_closure_set(v___f_396_, 4, v_toBind_385_);
lean_closure_set(v___f_396_, 5, v_getFileName_386_);
lean_closure_set(v___f_396_, 6, v_inst_387_);
lean_closure_set(v___f_396_, 7, v___f_388_);
lean_closure_set(v___f_396_, 8, v_ictx_395_);
lean_closure_set(v___f_396_, 9, v_source_379_);
lean_closure_set(v___f_396_, 10, v___f_389_);
lean_closure_set(v___f_396_, 11, v_env_390_);
lean_closure_set(v___f_396_, 12, v_val_391_);
lean_closure_set(v___f_396_, 13, v___y_381_);
lean_closure_set(v___f_396_, 14, v___x_392_);
v___x_397_ = lean_apply_4(v_toBind_385_, lean_box(0), lean_box(0), v_inst_393_, v___f_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_inst_398_, lean_object* v_source_399_, lean_object* v_text_400_, lean_object* v___y_401_, lean_object* v_inst_402_, lean_object* v_toApplicative_403_, lean_object* v_toBind_404_, lean_object* v_inst_405_, lean_object* v___f_406_, lean_object* v___f_407_, lean_object* v_val_408_, lean_object* v___x_409_, lean_object* v_inst_410_, lean_object* v_env_411_){
_start:
{
lean_object* v_getFileName_412_; lean_object* v_logMessage_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_getFileName_412_ = lean_ctor_get(v_inst_398_, 2);
lean_inc_n(v_getFileName_412_, 2);
v_logMessage_413_ = lean_ctor_get(v_inst_398_, 4);
lean_inc(v_logMessage_413_);
lean_dec_ref(v_inst_398_);
lean_inc(v_toBind_404_);
v___f_414_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 16, 15);
lean_closure_set(v___f_414_, 0, v_source_399_);
lean_closure_set(v___f_414_, 1, v_text_400_);
lean_closure_set(v___f_414_, 2, v___y_401_);
lean_closure_set(v___f_414_, 3, v_inst_402_);
lean_closure_set(v___f_414_, 4, v_toApplicative_403_);
lean_closure_set(v___f_414_, 5, v_logMessage_413_);
lean_closure_set(v___f_414_, 6, v_toBind_404_);
lean_closure_set(v___f_414_, 7, v_getFileName_412_);
lean_closure_set(v___f_414_, 8, v_inst_405_);
lean_closure_set(v___f_414_, 9, v___f_406_);
lean_closure_set(v___f_414_, 10, v___f_407_);
lean_closure_set(v___f_414_, 11, v_env_411_);
lean_closure_set(v___f_414_, 12, v_val_408_);
lean_closure_set(v___f_414_, 13, v___x_409_);
lean_closure_set(v___f_414_, 14, v_inst_410_);
v___x_415_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v_getFileName_412_, v___f_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__11___closed__0));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* v_docComment_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_toApplicative_423_, lean_object* v_toBind_424_, lean_object* v_inst_425_, lean_object* v___f_426_, lean_object* v___f_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_text_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; lean_object* v___x_434_; 
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = l_Lean_Syntax_getArg(v_docComment_419_, v___x_431_);
v___x_433_ = 1;
v___x_434_ = l_Lean_Syntax_getPos_x3f(v___x_432_, v___x_433_);
if (lean_obj_tag(v___x_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_436_; 
v_val_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_val_435_);
lean_dec_ref(v___x_434_);
v___x_436_ = l_Lean_Syntax_getTailPos_x3f(v___x_432_, v___x_433_);
lean_dec(v___x_432_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; lean_object* v_source_438_; lean_object* v___y_440_; lean_object* v___x_444_; lean_object* v_endPos_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
lean_dec_ref(v_inst_429_);
lean_dec(v_docComment_419_);
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref(v___x_436_);
v_source_438_ = lean_ctor_get(v_text_430_, 0);
lean_inc_ref(v_source_438_);
v___x_444_ = lean_string_utf8_prev(v_source_438_, v_val_437_);
lean_dec(v_val_437_);
v_endPos_445_ = lean_string_utf8_prev(v_source_438_, v___x_444_);
lean_dec(v___x_444_);
v___x_446_ = lean_string_utf8_byte_size(v_source_438_);
v___x_447_ = lean_nat_dec_le(v_endPos_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_dec(v_endPos_445_);
v___y_440_ = v___x_446_;
goto v___jp_439_;
}
else
{
v___y_440_ = v_endPos_445_;
goto v___jp_439_;
}
v___jp_439_:
{
lean_object* v_getEnv_441_; lean_object* v___f_442_; lean_object* v___x_443_; 
v_getEnv_441_ = lean_ctor_get(v_inst_420_, 0);
lean_inc(v_getEnv_441_);
lean_dec_ref(v_inst_420_);
lean_inc(v_toBind_424_);
v___f_442_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 14, 13);
lean_closure_set(v___f_442_, 0, v_inst_421_);
lean_closure_set(v___f_442_, 1, v_source_438_);
lean_closure_set(v___f_442_, 2, v_text_430_);
lean_closure_set(v___f_442_, 3, v___y_440_);
lean_closure_set(v___f_442_, 4, v_inst_422_);
lean_closure_set(v___f_442_, 5, v_toApplicative_423_);
lean_closure_set(v___f_442_, 6, v_toBind_424_);
lean_closure_set(v___f_442_, 7, v_inst_425_);
lean_closure_set(v___f_442_, 8, v___f_426_);
lean_closure_set(v___f_442_, 9, v___f_427_);
lean_closure_set(v___f_442_, 10, v_val_435_);
lean_closure_set(v___f_442_, 11, v___x_431_);
lean_closure_set(v___f_442_, 12, v_inst_428_);
v___x_443_ = lean_apply_4(v_toBind_424_, lean_box(0), lean_box(0), v_getEnv_441_, v___f_442_);
return v___x_443_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v___x_436_);
lean_dec(v_val_435_);
lean_dec_ref(v_text_430_);
lean_dec(v_inst_428_);
lean_dec(v___f_427_);
lean_dec(v___f_426_);
lean_dec(v_toBind_424_);
lean_dec_ref(v_toApplicative_423_);
lean_dec_ref(v_inst_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
v___x_448_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_449_ = l_Lean_throwErrorAt___redArg(v_inst_425_, v_inst_429_, v_docComment_419_, v___x_448_);
return v___x_449_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v___x_434_);
lean_dec(v___x_432_);
lean_dec_ref(v_text_430_);
lean_dec(v_inst_428_);
lean_dec(v___f_427_);
lean_dec(v___f_426_);
lean_dec(v_toBind_424_);
lean_dec_ref(v_toApplicative_423_);
lean_dec_ref(v_inst_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
v___x_450_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_451_ = l_Lean_throwErrorAt___redArg(v_inst_425_, v_inst_429_, v_docComment_419_, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_docComment_469_){
_start:
{
lean_object* v_toApplicative_470_; lean_object* v_toBind_471_; lean_object* v___f_472_; lean_object* v___f_473_; lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_toApplicative_470_ = lean_ctor_get(v_inst_462_, 0);
lean_inc_ref_n(v_toApplicative_470_, 4);
v_toBind_471_ = lean_ctor_get(v_inst_462_, 1);
lean_inc_n(v_toBind_471_, 2);
v___f_472_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_472_, 0, v_toApplicative_470_);
v___f_473_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_473_, 0, v_toApplicative_470_);
lean_inc_n(v_docComment_469_, 2);
v___f_474_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 12, 11);
lean_closure_set(v___f_474_, 0, v_docComment_469_);
lean_closure_set(v___f_474_, 1, v_inst_465_);
lean_closure_set(v___f_474_, 2, v_inst_467_);
lean_closure_set(v___f_474_, 3, v_inst_468_);
lean_closure_set(v___f_474_, 4, v_toApplicative_470_);
lean_closure_set(v___f_474_, 5, v_toBind_471_);
lean_closure_set(v___f_474_, 6, v_inst_462_);
lean_closure_set(v___f_474_, 7, v___f_472_);
lean_closure_set(v___f_474_, 8, v___f_473_);
lean_closure_set(v___f_474_, 9, v_inst_466_);
lean_closure_set(v___f_474_, 10, v_inst_464_);
v___x_475_ = l_Lean_Syntax_getKind(v_docComment_469_);
v___x_476_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_477_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_478_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_479_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_480_ = lean_name_eq(v___x_475_, v___x_479_);
lean_dec(v___x_475_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v_toApplicative_470_);
lean_dec(v_docComment_469_);
v___x_481_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = l_Lean_Syntax_getArg(v_docComment_469_, v___x_482_);
lean_dec(v_docComment_469_);
if (lean_obj_tag(v___x_483_) == 1)
{
lean_object* v_kind_484_; 
v_kind_484_ = lean_ctor_get(v___x_483_, 1);
lean_inc(v_kind_484_);
if (lean_obj_tag(v_kind_484_) == 1)
{
lean_object* v_pre_485_; 
v_pre_485_ = lean_ctor_get(v_kind_484_, 0);
lean_inc(v_pre_485_);
if (lean_obj_tag(v_pre_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_pre_485_, 0);
lean_inc(v_pre_486_);
if (lean_obj_tag(v_pre_486_) == 1)
{
lean_object* v_pre_487_; 
v_pre_487_ = lean_ctor_get(v_pre_486_, 0);
lean_inc(v_pre_487_);
if (lean_obj_tag(v_pre_487_) == 1)
{
lean_object* v_pre_488_; 
v_pre_488_ = lean_ctor_get(v_pre_487_, 0);
lean_inc(v_pre_488_);
if (lean_obj_tag(v_pre_488_) == 0)
{
lean_object* v_info_489_; lean_object* v_args_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_522_; 
v_info_489_ = lean_ctor_get(v___x_483_, 0);
v_args_490_ = lean_ctor_get(v___x_483_, 2);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_483_, 1);
lean_dec(v_unused_523_);
v___x_492_ = v___x_483_;
v_isShared_493_ = v_isSharedCheck_522_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_args_490_);
lean_inc(v_info_489_);
lean_dec(v___x_483_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_522_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_str_494_; lean_object* v_str_495_; lean_object* v_str_496_; lean_object* v_str_497_; uint8_t v___x_498_; 
v_str_494_ = lean_ctor_get(v_kind_484_, 1);
lean_inc_ref(v_str_494_);
lean_dec_ref(v_kind_484_);
v_str_495_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_495_);
lean_dec_ref(v_pre_485_);
v_str_496_ = lean_ctor_get(v_pre_486_, 1);
lean_inc_ref(v_str_496_);
lean_dec_ref(v_pre_486_);
v_str_497_ = lean_ctor_get(v_pre_487_, 1);
lean_inc_ref(v_str_497_);
lean_dec_ref(v_pre_487_);
v___x_498_ = lean_string_dec_eq(v_str_497_, v___x_476_);
lean_dec_ref(v_str_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec_ref(v_str_496_);
lean_dec_ref(v_str_495_);
lean_dec_ref(v_str_494_);
lean_del_object(v___x_492_);
lean_dec_ref(v_args_490_);
lean_dec(v_info_489_);
lean_dec_ref(v_toApplicative_470_);
v___x_499_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_499_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = lean_string_dec_eq(v_str_496_, v___x_477_);
lean_dec_ref(v_str_496_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec_ref(v_str_495_);
lean_dec_ref(v_str_494_);
lean_del_object(v___x_492_);
lean_dec_ref(v_args_490_);
lean_dec(v_info_489_);
lean_dec_ref(v_toApplicative_470_);
v___x_501_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_501_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = lean_string_dec_eq(v_str_495_, v___x_478_);
lean_dec_ref(v_str_495_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec_ref(v_str_494_);
lean_del_object(v___x_492_);
lean_dec_ref(v_args_490_);
lean_dec(v_info_489_);
lean_dec_ref(v_toApplicative_470_);
v___x_503_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_505_ = lean_string_dec_eq(v_str_494_, v___x_504_);
lean_dec_ref(v_str_494_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_del_object(v___x_492_);
lean_dec_ref(v_args_490_);
lean_dec(v_info_489_);
lean_dec_ref(v_toApplicative_470_);
v___x_506_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_506_;
}
else
{
lean_dec_ref(v___f_474_);
lean_dec(v_toBind_471_);
lean_dec(v_inst_463_);
if (v___x_505_ == 0)
{
lean_object* v_toPure_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_del_object(v___x_492_);
lean_dec_ref(v_args_490_);
lean_dec(v_info_489_);
v_toPure_507_ = lean_ctor_get(v_toApplicative_470_, 1);
lean_inc(v_toPure_507_);
lean_dec_ref(v_toApplicative_470_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_apply_2(v_toPure_507_, lean_box(0), v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_toPure_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v_toPure_510_ = lean_ctor_get(v_toApplicative_470_, 1);
lean_inc(v_toPure_510_);
lean_dec_ref(v_toApplicative_470_);
v___x_511_ = l_Lean_Name_str___override(v_pre_488_, v___x_476_);
v___x_512_ = l_Lean_Name_str___override(v___x_511_, v___x_477_);
v___x_513_ = l_Lean_Name_str___override(v___x_512_, v___x_478_);
v___x_514_ = l_Lean_Name_str___override(v___x_513_, v___x_504_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 1, v___x_514_);
v___x_516_ = v___x_492_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_info_489_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_args_490_);
v___x_516_ = v_reuseFailAlloc_521_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = l_Lean_Syntax_getArg(v___x_516_, v___x_517_);
lean_dec_ref(v___x_516_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_apply_2(v_toPure_510_, lean_box(0), v___x_519_);
return v___x_520_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_524_; 
lean_dec_ref(v_pre_487_);
lean_dec(v_pre_488_);
lean_dec_ref(v_pre_486_);
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_kind_484_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_524_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v_pre_487_);
lean_dec_ref(v_pre_486_);
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_kind_484_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_525_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec_ref(v_pre_485_);
lean_dec(v_pre_486_);
lean_dec_ref(v_kind_484_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_526_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec_ref(v_kind_484_);
lean_dec(v_pre_485_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_527_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v_kind_484_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_528_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; 
lean_dec(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_529_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_docComment_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_parseVersoDocString___redArg(v_inst_531_, v_inst_532_, v_inst_533_, v_inst_534_, v_inst_535_, v_inst_536_, v_inst_537_, v_docComment_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v___y_540_, lean_object* v_text_541_, lean_object* v_source_542_, lean_object* v_logMessage_543_, lean_object* v_____do__lift_544_){
_start:
{
lean_object* v_pos_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint32_t v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_pos_545_ = lean_ctor_get(v___y_540_, 2);
v___x_546_ = l_Lean_FileMap_toPosition(v_text_541_, v_pos_545_);
v___x_547_ = lean_box(0);
v___x_548_ = 0;
v___x_549_ = 2;
v___x_550_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_551_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_552_ = lean_string_utf8_get(v_source_542_, v_pos_545_);
v___x_553_ = lean_string_push(v___x_550_, v___x_552_);
v___x_554_ = lean_string_append(v___x_551_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_556_ = lean_string_append(v___x_554_, v___x_555_);
v___x_557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = l_Lean_MessageData_ofFormat(v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_559_, 0, v_____do__lift_544_);
lean_ctor_set(v___x_559_, 1, v___x_546_);
lean_ctor_set(v___x_559_, 2, v___x_547_);
lean_ctor_set(v___x_559_, 3, v___x_550_);
lean_ctor_set(v___x_559_, 4, v___x_558_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5, v___x_548_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5 + 1, v___x_549_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*5 + 2, v___x_548_);
v___x_560_ = lean_apply_1(v_logMessage_543_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v___y_561_, lean_object* v_text_562_, lean_object* v_source_563_, lean_object* v_logMessage_564_, lean_object* v_____do__lift_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v___y_561_, v_text_562_, v_source_563_, v_logMessage_564_, v_____do__lift_565_);
lean_dec_ref(v_source_563_);
lean_dec_ref(v___y_561_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v_toPure_567_, lean_object* v_toBind_568_, lean_object* v_getFileName_569_, lean_object* v___f_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v___y_573_, lean_object* v_ictx_574_, lean_object* v_____s_575_){
_start:
{
uint8_t v___y_580_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_array_get_size(v___x_571_);
v___x_583_ = lean_nat_dec_eq(v___x_582_, v___x_572_);
if (v___x_583_ == 0)
{
v___y_580_ = v___x_583_;
goto v___jp_579_;
}
else
{
lean_object* v_pos_584_; uint8_t v___x_585_; 
v_pos_584_ = lean_ctor_get(v___y_573_, 2);
v___x_585_ = l_Lean_Parser_InputContext_atEnd(v_ictx_574_, v_pos_584_);
if (v___x_585_ == 0)
{
v___y_580_ = v___x_583_;
goto v___jp_579_;
}
else
{
lean_dec(v___f_570_);
lean_dec(v_getFileName_569_);
lean_dec(v_toBind_568_);
goto v___jp_576_;
}
}
v___jp_576_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_box(0);
v___x_578_ = lean_apply_2(v_toPure_567_, lean_box(0), v___x_577_);
return v___x_578_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_dec(v___f_570_);
lean_dec(v_getFileName_569_);
lean_dec(v_toBind_568_);
goto v___jp_576_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v_toPure_567_);
v___x_581_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v_getFileName_569_, v___f_570_);
return v___x_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object* v_toPure_586_, lean_object* v_toBind_587_, lean_object* v_getFileName_588_, lean_object* v___f_589_, lean_object* v___x_590_, lean_object* v___x_591_, lean_object* v___y_592_, lean_object* v_ictx_593_, lean_object* v_____s_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_reportVersoParseFailure___redArg___lam__1(v_toPure_586_, v_toBind_587_, v_getFileName_588_, v___f_589_, v___x_590_, v___x_591_, v___y_592_, v_ictx_593_, v_____s_594_);
lean_dec_ref(v_ictx_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___x_591_);
lean_dec_ref(v___x_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v___x_596_, lean_object* v_toPure_597_, lean_object* v_____r_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_596_);
v___x_600_ = lean_apply_2(v_toPure_597_, lean_box(0), v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_text_601_, lean_object* v_fst_602_, lean_object* v_snd_603_, lean_object* v_logMessage_604_, lean_object* v_toBind_605_, lean_object* v___f_606_, lean_object* v_____do__lift_607_){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_608_ = l_Lean_FileMap_toPosition(v_text_601_, v_fst_602_);
v___x_609_ = lean_box(0);
v___x_610_ = 0;
v___x_611_ = 2;
v___x_612_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_613_ = l_Lean_Parser_Error_toString(v_snd_603_);
v___x_614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = l_Lean_MessageData_ofFormat(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_616_, 0, v_____do__lift_607_);
lean_ctor_set(v___x_616_, 1, v___x_608_);
lean_ctor_set(v___x_616_, 2, v___x_609_);
lean_ctor_set(v___x_616_, 3, v___x_612_);
lean_ctor_set(v___x_616_, 4, v___x_615_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*5, v___x_610_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*5 + 1, v___x_611_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*5 + 2, v___x_610_);
v___x_617_ = lean_apply_1(v_logMessage_604_, v___x_616_);
v___x_618_ = lean_apply_4(v_toBind_605_, lean_box(0), lean_box(0), v___x_617_, v___f_606_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(lean_object* v_text_619_, lean_object* v_fst_620_, lean_object* v_snd_621_, lean_object* v_logMessage_622_, lean_object* v_toBind_623_, lean_object* v___f_624_, lean_object* v_____do__lift_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_reportVersoParseFailure___redArg___lam__3(v_text_619_, v_fst_620_, v_snd_621_, v_logMessage_622_, v_toBind_623_, v___f_624_, v_____do__lift_625_);
lean_dec(v_fst_620_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_text_627_, lean_object* v_logMessage_628_, lean_object* v_toBind_629_, lean_object* v___f_630_, lean_object* v_getFileName_631_, lean_object* v_a_632_, lean_object* v_x_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_snd_635_; lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___f_638_; lean_object* v___x_639_; 
v_snd_635_ = lean_ctor_get(v_a_632_, 1);
lean_inc(v_snd_635_);
v_fst_636_ = lean_ctor_get(v_a_632_, 0);
lean_inc(v_fst_636_);
lean_dec_ref(v_a_632_);
v_snd_637_ = lean_ctor_get(v_snd_635_, 1);
lean_inc(v_snd_637_);
lean_dec(v_snd_635_);
lean_inc(v_toBind_629_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_638_, 0, v_text_627_);
lean_closure_set(v___f_638_, 1, v_fst_636_);
lean_closure_set(v___f_638_, 2, v_snd_637_);
lean_closure_set(v___f_638_, 3, v_logMessage_628_);
lean_closure_set(v___f_638_, 4, v_toBind_629_);
lean_closure_set(v___f_638_, 5, v___f_630_);
v___x_639_ = lean_apply_4(v_toBind_629_, lean_box(0), lean_box(0), v_getFileName_631_, v___f_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_text_640_, lean_object* v_source_641_, lean_object* v_logMessage_642_, lean_object* v_toPure_643_, lean_object* v_toBind_644_, lean_object* v_getFileName_645_, lean_object* v___x_646_, lean_object* v_ictx_647_, lean_object* v_inst_648_, lean_object* v_env_649_, lean_object* v_____do__lift_650_, lean_object* v_____do__lift_651_, lean_object* v_val_652_, lean_object* v___y_653_, lean_object* v_____do__lift_654_){
_start:
{
lean_object* v___y_656_; lean_object* v_pmctx_667_; lean_object* v_blockCtxt_668_; lean_object* v___x_669_; lean_object* v_s_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_s_673_; uint8_t v___y_675_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
lean_inc_ref(v_env_649_);
v_pmctx_667_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_667_, 0, v_env_649_);
lean_ctor_set(v_pmctx_667_, 1, v_____do__lift_650_);
lean_ctor_set(v_pmctx_667_, 2, v_____do__lift_651_);
lean_ctor_set(v_pmctx_667_, 3, v_____do__lift_654_);
lean_inc(v_val_652_);
lean_inc_ref(v_text_640_);
v_blockCtxt_668_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_640_, v_val_652_, v___y_653_);
v___x_669_ = l_Lean_Parser_mkParserState(v_source_641_);
lean_inc_ref(v___x_669_);
v_s_670_ = l_Lean_Parser_ParserState_setPos(v___x_669_, v_val_652_);
v___x_671_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_671_, 0, v_blockCtxt_668_);
v___x_672_ = l_Lean_Parser_getTokenTable(v_env_649_);
lean_inc_ref(v___x_672_);
lean_inc_ref(v_pmctx_667_);
lean_inc_ref(v_ictx_647_);
v_s_673_ = l_Lean_Parser_ParserFn_run(v___x_671_, v_ictx_647_, v_pmctx_667_, v___x_672_, v_s_670_);
lean_inc_ref(v_s_673_);
v___x_685_ = l_Lean_Parser_ParserState_allErrors(v_s_673_);
v___x_686_ = lean_array_get_size(v___x_685_);
lean_dec_ref(v___x_685_);
v___x_687_ = lean_nat_dec_eq(v___x_686_, v___x_646_);
if (v___x_687_ == 0)
{
v___y_675_ = v___x_687_;
goto v___jp_674_;
}
else
{
lean_object* v_pos_688_; uint8_t v___x_689_; 
v_pos_688_ = lean_ctor_get(v_s_673_, 2);
lean_inc(v_pos_688_);
v___x_689_ = l_Lean_Parser_InputContext_atEnd(v_ictx_647_, v_pos_688_);
lean_dec(v_pos_688_);
if (v___x_689_ == 0)
{
v___y_675_ = v___x_687_;
goto v___jp_674_;
}
else
{
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_pmctx_667_);
v___y_656_ = v_s_673_;
goto v___jp_655_;
}
}
v___jp_655_:
{
lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___f_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___f_662_; size_t v_sz_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_inc(v_logMessage_642_);
lean_inc_ref(v_text_640_);
lean_inc_ref_n(v___y_656_, 2);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_657_, 0, v___y_656_);
lean_closure_set(v___f_657_, 1, v_text_640_);
lean_closure_set(v___f_657_, 2, v_source_641_);
lean_closure_set(v___f_657_, 3, v_logMessage_642_);
v___x_658_ = l_Lean_Parser_ParserState_allErrors(v___y_656_);
lean_inc_ref(v___x_658_);
lean_inc(v_getFileName_645_);
lean_inc_n(v_toBind_644_, 2);
lean_inc(v_toPure_643_);
v___f_659_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_659_, 0, v_toPure_643_);
lean_closure_set(v___f_659_, 1, v_toBind_644_);
lean_closure_set(v___f_659_, 2, v_getFileName_645_);
lean_closure_set(v___f_659_, 3, v___f_657_);
lean_closure_set(v___f_659_, 4, v___x_658_);
lean_closure_set(v___f_659_, 5, v___x_646_);
lean_closure_set(v___f_659_, 6, v___y_656_);
lean_closure_set(v___f_659_, 7, v_ictx_647_);
v___x_660_ = lean_box(0);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2), 3, 2);
lean_closure_set(v___f_661_, 0, v___x_660_);
lean_closure_set(v___f_661_, 1, v_toPure_643_);
v___f_662_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4), 8, 5);
lean_closure_set(v___f_662_, 0, v_text_640_);
lean_closure_set(v___f_662_, 1, v_logMessage_642_);
lean_closure_set(v___f_662_, 2, v_toBind_644_);
lean_closure_set(v___f_662_, 3, v___f_661_);
lean_closure_set(v___f_662_, 4, v_getFileName_645_);
v_sz_663_ = lean_array_size(v___x_658_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_648_, v___x_658_, v___f_662_, v_sz_663_, v___x_664_, v___x_660_);
v___x_666_ = lean_apply_4(v_toBind_644_, lean_box(0), lean_box(0), v___x_665_, v___f_659_);
return v___x_666_;
}
v___jp_674_:
{
if (v___y_675_ == 0)
{
lean_dec_ref(v___x_672_);
lean_dec_ref(v___x_669_);
lean_dec_ref(v_pmctx_667_);
v___y_656_ = v_s_673_;
goto v___jp_655_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v_pos_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_box(0);
v___x_678_ = lean_unsigned_to_nat(1u);
lean_inc_n(v___x_646_, 3);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v___x_646_);
v___x_680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_680_, 0, v___x_646_);
lean_ctor_set(v___x_680_, 1, v___x_676_);
lean_ctor_set(v___x_680_, 2, v___x_677_);
lean_ctor_set(v___x_680_, 3, v___x_679_);
lean_ctor_set(v___x_680_, 4, v___x_646_);
v_pos_681_ = lean_ctor_get(v_s_673_, 2);
lean_inc(v_pos_681_);
lean_dec_ref(v_s_673_);
v___x_682_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_682_, 0, v___x_680_);
v___x_683_ = l_Lean_Parser_ParserState_setPos(v___x_669_, v_pos_681_);
lean_inc_ref(v_ictx_647_);
v___x_684_ = l_Lean_Parser_ParserFn_run(v___x_682_, v_ictx_647_, v_pmctx_667_, v___x_672_, v___x_683_);
v___y_656_ = v___x_684_;
goto v___jp_655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_text_690_, lean_object* v_source_691_, lean_object* v_logMessage_692_, lean_object* v_toPure_693_, lean_object* v_toBind_694_, lean_object* v_getFileName_695_, lean_object* v___x_696_, lean_object* v_ictx_697_, lean_object* v_inst_698_, lean_object* v_env_699_, lean_object* v_____do__lift_700_, lean_object* v_val_701_, lean_object* v___y_702_, lean_object* v_getOpenDecls_703_, lean_object* v_____do__lift_704_){
_start:
{
lean_object* v___f_705_; lean_object* v___x_706_; 
lean_inc(v_toBind_694_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(v___f_705_, 0, v_text_690_);
lean_closure_set(v___f_705_, 1, v_source_691_);
lean_closure_set(v___f_705_, 2, v_logMessage_692_);
lean_closure_set(v___f_705_, 3, v_toPure_693_);
lean_closure_set(v___f_705_, 4, v_toBind_694_);
lean_closure_set(v___f_705_, 5, v_getFileName_695_);
lean_closure_set(v___f_705_, 6, v___x_696_);
lean_closure_set(v___f_705_, 7, v_ictx_697_);
lean_closure_set(v___f_705_, 8, v_inst_698_);
lean_closure_set(v___f_705_, 9, v_env_699_);
lean_closure_set(v___f_705_, 10, v_____do__lift_700_);
lean_closure_set(v___f_705_, 11, v_____do__lift_704_);
lean_closure_set(v___f_705_, 12, v_val_701_);
lean_closure_set(v___f_705_, 13, v___y_702_);
v___x_706_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v_getOpenDecls_703_, v___f_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_707_, lean_object* v_text_708_, lean_object* v_source_709_, lean_object* v_logMessage_710_, lean_object* v_toPure_711_, lean_object* v_toBind_712_, lean_object* v_getFileName_713_, lean_object* v___x_714_, lean_object* v_ictx_715_, lean_object* v_inst_716_, lean_object* v_env_717_, lean_object* v_val_718_, lean_object* v___y_719_, lean_object* v_____do__lift_720_){
_start:
{
lean_object* v_getCurrNamespace_721_; lean_object* v_getOpenDecls_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v_getCurrNamespace_721_ = lean_ctor_get(v_inst_707_, 0);
lean_inc(v_getCurrNamespace_721_);
v_getOpenDecls_722_ = lean_ctor_get(v_inst_707_, 1);
lean_inc(v_getOpenDecls_722_);
lean_dec_ref(v_inst_707_);
lean_inc(v_toBind_712_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 15, 14);
lean_closure_set(v___f_723_, 0, v_text_708_);
lean_closure_set(v___f_723_, 1, v_source_709_);
lean_closure_set(v___f_723_, 2, v_logMessage_710_);
lean_closure_set(v___f_723_, 3, v_toPure_711_);
lean_closure_set(v___f_723_, 4, v_toBind_712_);
lean_closure_set(v___f_723_, 5, v_getFileName_713_);
lean_closure_set(v___f_723_, 6, v___x_714_);
lean_closure_set(v___f_723_, 7, v_ictx_715_);
lean_closure_set(v___f_723_, 8, v_inst_716_);
lean_closure_set(v___f_723_, 9, v_env_717_);
lean_closure_set(v___f_723_, 10, v_____do__lift_720_);
lean_closure_set(v___f_723_, 11, v_val_718_);
lean_closure_set(v___f_723_, 12, v___y_719_);
lean_closure_set(v___f_723_, 13, v_getOpenDecls_722_);
v___x_724_ = lean_apply_4(v_toBind_712_, lean_box(0), lean_box(0), v_getCurrNamespace_721_, v___f_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_source_725_, lean_object* v_text_726_, lean_object* v___y_727_, lean_object* v_inst_728_, lean_object* v_logMessage_729_, lean_object* v_toPure_730_, lean_object* v_toBind_731_, lean_object* v_getFileName_732_, lean_object* v___x_733_, lean_object* v_inst_734_, lean_object* v_env_735_, lean_object* v_val_736_, lean_object* v_inst_737_, lean_object* v_____do__lift_738_){
_start:
{
lean_object* v_ictx_739_; lean_object* v___f_740_; lean_object* v___x_741_; 
lean_inc(v___y_727_);
lean_inc_ref(v_text_726_);
lean_inc_ref(v_source_725_);
v_ictx_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_739_, 0, v_source_725_);
lean_ctor_set(v_ictx_739_, 1, v_____do__lift_738_);
lean_ctor_set(v_ictx_739_, 2, v_text_726_);
lean_ctor_set(v_ictx_739_, 3, v___y_727_);
lean_inc(v_toBind_731_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 14, 13);
lean_closure_set(v___f_740_, 0, v_inst_728_);
lean_closure_set(v___f_740_, 1, v_text_726_);
lean_closure_set(v___f_740_, 2, v_source_725_);
lean_closure_set(v___f_740_, 3, v_logMessage_729_);
lean_closure_set(v___f_740_, 4, v_toPure_730_);
lean_closure_set(v___f_740_, 5, v_toBind_731_);
lean_closure_set(v___f_740_, 6, v_getFileName_732_);
lean_closure_set(v___f_740_, 7, v___x_733_);
lean_closure_set(v___f_740_, 8, v_ictx_739_);
lean_closure_set(v___f_740_, 9, v_inst_734_);
lean_closure_set(v___f_740_, 10, v_env_735_);
lean_closure_set(v___f_740_, 11, v_val_736_);
lean_closure_set(v___f_740_, 12, v___y_727_);
v___x_741_ = lean_apply_4(v_toBind_731_, lean_box(0), lean_box(0), v_inst_737_, v___f_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object* v_inst_742_, lean_object* v_source_743_, lean_object* v_text_744_, lean_object* v___y_745_, lean_object* v_inst_746_, lean_object* v_toPure_747_, lean_object* v_toBind_748_, lean_object* v___x_749_, lean_object* v_inst_750_, lean_object* v_val_751_, lean_object* v_inst_752_, lean_object* v_env_753_){
_start:
{
lean_object* v_getFileName_754_; lean_object* v_logMessage_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
v_getFileName_754_ = lean_ctor_get(v_inst_742_, 2);
lean_inc_n(v_getFileName_754_, 2);
v_logMessage_755_ = lean_ctor_get(v_inst_742_, 4);
lean_inc(v_logMessage_755_);
lean_dec_ref(v_inst_742_);
lean_inc(v_toBind_748_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 14, 13);
lean_closure_set(v___f_756_, 0, v_source_743_);
lean_closure_set(v___f_756_, 1, v_text_744_);
lean_closure_set(v___f_756_, 2, v___y_745_);
lean_closure_set(v___f_756_, 3, v_inst_746_);
lean_closure_set(v___f_756_, 4, v_logMessage_755_);
lean_closure_set(v___f_756_, 5, v_toPure_747_);
lean_closure_set(v___f_756_, 6, v_toBind_748_);
lean_closure_set(v___f_756_, 7, v_getFileName_754_);
lean_closure_set(v___f_756_, 8, v___x_749_);
lean_closure_set(v___f_756_, 9, v_inst_750_);
lean_closure_set(v___f_756_, 10, v_env_753_);
lean_closure_set(v___f_756_, 11, v_val_751_);
lean_closure_set(v___f_756_, 12, v_inst_752_);
v___x_757_ = lean_apply_4(v_toBind_748_, lean_box(0), lean_box(0), v_getFileName_754_, v___f_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_toPure_761_, lean_object* v_toBind_762_, lean_object* v___x_763_, lean_object* v_inst_764_, lean_object* v_val_765_, lean_object* v_inst_766_, lean_object* v_val_767_, lean_object* v_text_768_){
_start:
{
lean_object* v_source_769_; lean_object* v___y_771_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_source_769_ = lean_ctor_get(v_text_768_, 0);
lean_inc_ref(v_source_769_);
v___x_775_ = lean_string_utf8_byte_size(v_source_769_);
v___x_776_ = lean_nat_dec_le(v_val_767_, v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v_val_767_);
v___y_771_ = v___x_775_;
goto v___jp_770_;
}
else
{
v___y_771_ = v_val_767_;
goto v___jp_770_;
}
v___jp_770_:
{
lean_object* v_getEnv_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v_getEnv_772_ = lean_ctor_get(v_inst_758_, 0);
lean_inc(v_getEnv_772_);
lean_dec_ref(v_inst_758_);
lean_inc(v_toBind_762_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__9), 12, 11);
lean_closure_set(v___f_773_, 0, v_inst_759_);
lean_closure_set(v___f_773_, 1, v_source_769_);
lean_closure_set(v___f_773_, 2, v_text_768_);
lean_closure_set(v___f_773_, 3, v___y_771_);
lean_closure_set(v___f_773_, 4, v_inst_760_);
lean_closure_set(v___f_773_, 5, v_toPure_761_);
lean_closure_set(v___f_773_, 6, v_toBind_762_);
lean_closure_set(v___f_773_, 7, v___x_763_);
lean_closure_set(v___f_773_, 8, v_inst_764_);
lean_closure_set(v___f_773_, 9, v_val_765_);
lean_closure_set(v___f_773_, 10, v_inst_766_);
v___x_774_ = lean_apply_4(v_toBind_762_, lean_box(0), lean_box(0), v_getEnv_772_, v___f_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_parseFailure_783_){
_start:
{
lean_object* v_toApplicative_784_; lean_object* v_toBind_785_; lean_object* v_toPure_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v_toApplicative_784_ = lean_ctor_get(v_inst_777_, 0);
v_toBind_785_ = lean_ctor_get(v_inst_777_, 1);
lean_inc(v_toBind_785_);
v_toPure_786_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_inc(v_toPure_786_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_Lean_Syntax_getArg(v_parseFailure_783_, v___x_787_);
v___x_789_ = 1;
v___x_790_ = l_Lean_Syntax_getPos_x3f(v___x_788_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 1)
{
lean_object* v_val_791_; lean_object* v___x_792_; 
v_val_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_val_791_);
lean_dec_ref(v___x_790_);
v___x_792_ = l_Lean_Syntax_getTailPos_x3f(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_val_793_; lean_object* v___f_794_; lean_object* v___x_795_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_793_);
lean_dec_ref(v___x_792_);
lean_inc(v_toBind_785_);
v___f_794_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__10), 11, 10);
lean_closure_set(v___f_794_, 0, v_inst_779_);
lean_closure_set(v___f_794_, 1, v_inst_781_);
lean_closure_set(v___f_794_, 2, v_inst_782_);
lean_closure_set(v___f_794_, 3, v_toPure_786_);
lean_closure_set(v___f_794_, 4, v_toBind_785_);
lean_closure_set(v___f_794_, 5, v___x_787_);
lean_closure_set(v___f_794_, 6, v_inst_777_);
lean_closure_set(v___f_794_, 7, v_val_791_);
lean_closure_set(v___f_794_, 8, v_inst_780_);
lean_closure_set(v___f_794_, 9, v_val_793_);
v___x_795_ = lean_apply_4(v_toBind_785_, lean_box(0), lean_box(0), v_inst_778_, v___f_794_);
return v___x_795_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v___x_792_);
lean_dec(v_val_791_);
lean_dec(v_toBind_785_);
lean_dec_ref(v_inst_782_);
lean_dec_ref(v_inst_781_);
lean_dec(v_inst_780_);
lean_dec_ref(v_inst_779_);
lean_dec(v_inst_778_);
lean_dec_ref(v_inst_777_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_apply_2(v_toPure_786_, lean_box(0), v___x_796_);
return v___x_797_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec(v___x_790_);
lean_dec(v___x_788_);
lean_dec(v_toBind_785_);
lean_dec_ref(v_inst_782_);
lean_dec_ref(v_inst_781_);
lean_dec(v_inst_780_);
lean_dec_ref(v_inst_779_);
lean_dec(v_inst_778_);
lean_dec_ref(v_inst_777_);
v___x_798_ = lean_box(0);
v___x_799_ = lean_apply_2(v_toPure_786_, lean_box(0), v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_parseFailure_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_reportVersoParseFailure___redArg(v_inst_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_, v_parseFailure_806_);
lean_dec(v_parseFailure_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_parseFailure_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_reportVersoParseFailure___redArg(v_inst_809_, v_inst_810_, v_inst_812_, v_inst_813_, v_inst_814_, v_inst_815_, v_parseFailure_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_parseFailure_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_reportVersoParseFailure(v_m_818_, v_inst_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_inst_823_, v_inst_824_, v_inst_825_, v_parseFailure_826_);
lean_dec(v_parseFailure_826_);
lean_dec_ref(v_inst_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_828_, size_t v_i_829_, lean_object* v_bs_830_){
_start:
{
uint8_t v___x_831_; 
v___x_831_ = lean_usize_dec_lt(v_i_829_, v_sz_828_);
if (v___x_831_ == 0)
{
return v_bs_830_;
}
else
{
lean_object* v_v_832_; lean_object* v___x_833_; lean_object* v_bs_x27_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_v_832_ = lean_array_uget(v_bs_830_, v_i_829_);
v___x_833_ = lean_unsigned_to_nat(0u);
v_bs_x27_834_ = lean_array_uset(v_bs_830_, v_i_829_, v___x_833_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_i_829_, v___x_835_);
v___x_837_ = lean_array_uset(v_bs_x27_834_, v_i_829_, v_v_832_);
v_i_829_ = v___x_836_;
v_bs_830_ = v___x_837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_839_, lean_object* v_i_840_, lean_object* v_bs_841_){
_start:
{
size_t v_sz_boxed_842_; size_t v_i_boxed_843_; lean_object* v_res_844_; 
v_sz_boxed_842_ = lean_unbox_usize(v_sz_839_);
lean_dec(v_sz_839_);
v_i_boxed_843_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_res_844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_842_, v_i_boxed_843_, v_bs_841_);
return v_res_844_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v___x_853_, uint8_t v_suppressElabErrors_854_, lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 1)
{
lean_object* v_pre_856_; 
v_pre_856_ = lean_ctor_get(v_x_855_, 0);
switch(lean_obj_tag(v_pre_856_))
{
case 1:
{
lean_object* v_pre_857_; 
v_pre_857_ = lean_ctor_get(v_pre_856_, 0);
switch(lean_obj_tag(v_pre_857_))
{
case 0:
{
lean_object* v_str_858_; lean_object* v_str_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_str_858_ = lean_ctor_get(v_x_855_, 1);
v_str_859_ = lean_ctor_get(v_pre_856_, 1);
v___x_860_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_861_ = lean_string_dec_eq(v_str_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_863_ = lean_string_dec_eq(v_str_859_, v___x_862_);
if (v___x_863_ == 0)
{
return v___x_853_;
}
else
{
lean_object* v___x_864_; uint8_t v___x_865_; 
v___x_864_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_865_ = lean_string_dec_eq(v_str_858_, v___x_864_);
if (v___x_865_ == 0)
{
return v___x_853_;
}
else
{
return v_suppressElabErrors_854_;
}
}
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_867_ = lean_string_dec_eq(v_str_858_, v___x_866_);
if (v___x_867_ == 0)
{
return v___x_853_;
}
else
{
return v_suppressElabErrors_854_;
}
}
}
case 1:
{
lean_object* v_pre_868_; 
v_pre_868_ = lean_ctor_get(v_pre_857_, 0);
if (lean_obj_tag(v_pre_868_) == 0)
{
lean_object* v_str_869_; lean_object* v_str_870_; lean_object* v_str_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_str_869_ = lean_ctor_get(v_x_855_, 1);
v_str_870_ = lean_ctor_get(v_pre_856_, 1);
v_str_871_ = lean_ctor_get(v_pre_857_, 1);
v___x_872_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_873_ = lean_string_dec_eq(v_str_871_, v___x_872_);
if (v___x_873_ == 0)
{
return v___x_853_;
}
else
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_875_ = lean_string_dec_eq(v_str_870_, v___x_874_);
if (v___x_875_ == 0)
{
return v___x_853_;
}
else
{
lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_877_ = lean_string_dec_eq(v_str_869_, v___x_876_);
if (v___x_877_ == 0)
{
return v___x_853_;
}
else
{
return v_suppressElabErrors_854_;
}
}
}
}
else
{
return v___x_853_;
}
}
default: 
{
return v___x_853_;
}
}
}
case 0:
{
lean_object* v_str_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_str_878_ = lean_ctor_get(v_x_855_, 1);
v___x_879_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_880_ = lean_string_dec_eq(v_str_878_, v___x_879_);
if (v___x_880_ == 0)
{
return v___x_853_;
}
else
{
return v_suppressElabErrors_854_;
}
}
default: 
{
return v___x_853_;
}
}
}
else
{
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v___x_881_, lean_object* v_suppressElabErrors_882_, lean_object* v_x_883_){
_start:
{
uint8_t v___x_10525__boxed_884_; uint8_t v_suppressElabErrors_boxed_885_; uint8_t v_res_886_; lean_object* v_r_887_; 
v___x_10525__boxed_884_ = lean_unbox(v___x_881_);
v_suppressElabErrors_boxed_885_ = lean_unbox(v_suppressElabErrors_882_);
v_res_886_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_10525__boxed_884_, v_suppressElabErrors_boxed_885_, v_x_883_);
lean_dec(v_x_883_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v___x_888_, uint8_t v_suppressElabErrors_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_890_) == 1)
{
lean_object* v_pre_891_; 
v_pre_891_ = lean_ctor_get(v_x_890_, 0);
switch(lean_obj_tag(v_pre_891_))
{
case 1:
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_pre_891_, 0);
switch(lean_obj_tag(v_pre_892_))
{
case 0:
{
lean_object* v_str_893_; lean_object* v_str_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_str_893_ = lean_ctor_get(v_x_890_, 1);
v_str_894_ = lean_ctor_get(v_pre_891_, 1);
v___x_895_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_896_ = lean_string_dec_eq(v_str_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_898_ = lean_string_dec_eq(v_str_894_, v___x_897_);
if (v___x_898_ == 0)
{
return v___x_888_;
}
else
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_900_ = lean_string_dec_eq(v_str_893_, v___x_899_);
if (v___x_900_ == 0)
{
return v___x_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_902_ = lean_string_dec_eq(v_str_893_, v___x_901_);
if (v___x_902_ == 0)
{
return v___x_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
case 1:
{
lean_object* v_pre_903_; 
v_pre_903_ = lean_ctor_get(v_pre_892_, 0);
if (lean_obj_tag(v_pre_903_) == 0)
{
lean_object* v_str_904_; lean_object* v_str_905_; lean_object* v_str_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_str_904_ = lean_ctor_get(v_x_890_, 1);
v_str_905_ = lean_ctor_get(v_pre_891_, 1);
v_str_906_ = lean_ctor_get(v_pre_892_, 1);
v___x_907_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_908_ = lean_string_dec_eq(v_str_906_, v___x_907_);
if (v___x_908_ == 0)
{
return v___x_888_;
}
else
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_910_ = lean_string_dec_eq(v_str_905_, v___x_909_);
if (v___x_910_ == 0)
{
return v___x_888_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_912_ = lean_string_dec_eq(v_str_904_, v___x_911_);
if (v___x_912_ == 0)
{
return v___x_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
}
}
else
{
return v___x_888_;
}
}
default: 
{
return v___x_888_;
}
}
}
case 0:
{
lean_object* v_str_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_str_913_ = lean_ctor_get(v_x_890_, 1);
v___x_914_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_915_ = lean_string_dec_eq(v_str_913_, v___x_914_);
if (v___x_915_ == 0)
{
return v___x_888_;
}
else
{
return v_suppressElabErrors_889_;
}
}
default: 
{
return v___x_888_;
}
}
}
else
{
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___x_916_, lean_object* v_suppressElabErrors_917_, lean_object* v_x_918_){
_start:
{
uint8_t v___x_10597__boxed_919_; uint8_t v_suppressElabErrors_boxed_920_; uint8_t v_res_921_; lean_object* v_r_922_; 
v___x_10597__boxed_919_ = lean_unbox(v___x_916_);
v_suppressElabErrors_boxed_920_ = lean_unbox(v_suppressElabErrors_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10597__boxed_919_, v_suppressElabErrors_boxed_920_, v_x_918_);
lean_dec(v_x_918_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v_as_925_, size_t v_sz_926_, size_t v_i_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v_a_933_; uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_927_, v_sz_926_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v___x_923_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_b_928_);
return v___x_938_;
}
else
{
lean_object* v_a_939_; lean_object* v_snd_940_; lean_object* v_fst_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_998_; 
v_a_939_ = lean_array_uget(v_as_925_, v_i_927_);
v_snd_940_ = lean_ctor_get(v_a_939_, 1);
v_fst_941_ = lean_ctor_get(v_a_939_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_998_ == 0)
{
v___x_943_ = v_a_939_;
v_isShared_944_ = v_isSharedCheck_998_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_941_);
lean_dec(v_a_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_998_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_996_; 
v_snd_945_ = lean_ctor_get(v_snd_940_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_snd_940_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v_snd_940_, 0);
lean_dec(v_unused_997_);
v___x_947_ = v_snd_940_;
v_isShared_948_ = v_isSharedCheck_996_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_dec(v_snd_940_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_996_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_fileName_949_; uint8_t v_suppressElabErrors_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v___y_963_; 
v_fileName_949_ = lean_ctor_get(v___y_929_, 0);
v_suppressElabErrors_950_ = lean_ctor_get_uint8(v___y_929_, sizeof(void*)*14 + 1);
v___x_951_ = lean_box(0);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_nat_dec_eq(v___x_924_, v___x_952_);
lean_inc_ref(v___x_923_);
v___x_954_ = l_Lean_FileMap_toPosition(v___x_923_, v_fst_941_);
lean_dec(v_fst_941_);
v___x_955_ = lean_box(0);
v___x_956_ = 2;
v___x_957_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_958_ = l_Lean_Parser_Error_toString(v_snd_945_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
if (v_suppressElabErrors_950_ == 0)
{
v___y_962_ = v___y_929_;
v___y_963_ = v___y_930_;
goto v___jp_961_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___f_994_; uint8_t v___x_995_; 
v___x_992_ = lean_box(v___x_953_);
v___x_993_ = lean_box(v_suppressElabErrors_950_);
v___f_994_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_994_, 0, v___x_992_);
lean_closure_set(v___f_994_, 1, v___x_993_);
lean_inc_ref(v___x_960_);
v___x_995_ = l_Lean_MessageData_hasTag(v___f_994_, v___x_960_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___x_960_);
lean_dec_ref(v___x_954_);
lean_del_object(v___x_947_);
lean_del_object(v___x_943_);
v_a_933_ = v___x_951_;
goto v___jp_932_;
}
else
{
v___y_962_ = v___y_929_;
v___y_963_ = v___y_930_;
goto v___jp_961_;
}
}
v___jp_961_:
{
lean_object* v___x_964_; lean_object* v_currNamespace_965_; lean_object* v_openDecls_966_; lean_object* v___x_968_; 
v___x_964_ = lean_st_ref_take(v___y_963_);
v_currNamespace_965_ = lean_ctor_get(v___y_962_, 6);
v_openDecls_966_ = lean_ctor_get(v___y_962_, 7);
lean_inc(v_openDecls_966_);
lean_inc(v_currNamespace_965_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_openDecls_966_);
lean_ctor_set(v___x_947_, 0, v_currNamespace_965_);
v___x_968_ = v___x_947_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_currNamespace_965_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v_openDecls_966_);
v___x_968_ = v_reuseFailAlloc_991_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 4);
lean_ctor_set(v___x_943_, 1, v___x_960_);
lean_ctor_set(v___x_943_, 0, v___x_968_);
v___x_970_ = v___x_943_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_960_);
v___x_970_ = v_reuseFailAlloc_990_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_cache_977_; lean_object* v_messages_978_; lean_object* v_infoState_979_; lean_object* v_snapshotTasks_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_989_; 
lean_inc_ref(v_fileName_949_);
v___x_971_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_971_, 0, v_fileName_949_);
lean_ctor_set(v___x_971_, 1, v___x_954_);
lean_ctor_set(v___x_971_, 2, v___x_955_);
lean_ctor_set(v___x_971_, 3, v___x_957_);
lean_ctor_set(v___x_971_, 4, v___x_970_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*5, v___x_953_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*5 + 1, v___x_956_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*5 + 2, v___x_953_);
v_env_972_ = lean_ctor_get(v___x_964_, 0);
v_nextMacroScope_973_ = lean_ctor_get(v___x_964_, 1);
v_ngen_974_ = lean_ctor_get(v___x_964_, 2);
v_auxDeclNGen_975_ = lean_ctor_get(v___x_964_, 3);
v_traceState_976_ = lean_ctor_get(v___x_964_, 4);
v_cache_977_ = lean_ctor_get(v___x_964_, 5);
v_messages_978_ = lean_ctor_get(v___x_964_, 6);
v_infoState_979_ = lean_ctor_get(v___x_964_, 7);
v_snapshotTasks_980_ = lean_ctor_get(v___x_964_, 8);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_989_ == 0)
{
v___x_982_ = v___x_964_;
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snapshotTasks_980_);
lean_inc(v_infoState_979_);
lean_inc(v_messages_978_);
lean_inc(v_cache_977_);
lean_inc(v_traceState_976_);
lean_inc(v_auxDeclNGen_975_);
lean_inc(v_ngen_974_);
lean_inc(v_nextMacroScope_973_);
lean_inc(v_env_972_);
lean_dec(v___x_964_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_989_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_MessageLog_add(v___x_971_, v_messages_978_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 6, v___x_984_);
v___x_986_ = v___x_982_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_env_972_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_nextMacroScope_973_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_ngen_974_);
lean_ctor_set(v_reuseFailAlloc_988_, 3, v_auxDeclNGen_975_);
lean_ctor_set(v_reuseFailAlloc_988_, 4, v_traceState_976_);
lean_ctor_set(v_reuseFailAlloc_988_, 5, v_cache_977_);
lean_ctor_set(v_reuseFailAlloc_988_, 6, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 7, v_infoState_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 8, v_snapshotTasks_980_);
v___x_986_ = v_reuseFailAlloc_988_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; 
v___x_987_ = lean_st_ref_set(v___y_963_, v___x_986_);
v_a_933_ = v___x_951_;
goto v___jp_932_;
}
}
}
}
}
}
}
}
v___jp_932_:
{
size_t v___x_934_; size_t v___x_935_; 
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_927_, v___x_934_);
v_i_927_ = v___x_935_;
v_b_928_ = v_a_933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_999_, lean_object* v___x_1000_, lean_object* v_as_1001_, lean_object* v_sz_1002_, lean_object* v_i_1003_, lean_object* v_b_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
size_t v_sz_boxed_1008_; size_t v_i_boxed_1009_; lean_object* v_res_1010_; 
v_sz_boxed_1008_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1009_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_999_, v___x_1000_, v_as_1001_, v_sz_boxed_1008_, v_i_boxed_1009_, v_b_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v_as_1001_);
lean_dec(v___x_1000_);
return v_res_1010_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_box(1);
v___x_1012_ = l_Lean_MessageData_ofFormat(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2));
v___x_1017_ = l_Lean_MessageData_ofFormat(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_x_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
return v_x_1018_;
}
else
{
lean_object* v_head_1020_; lean_object* v_tail_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1043_; 
v_head_1020_ = lean_ctor_get(v_x_1019_, 0);
v_tail_1021_ = lean_ctor_get(v_x_1019_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1023_ = v_x_1019_;
v_isShared_1024_ = v_isSharedCheck_1043_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_tail_1021_);
lean_inc(v_head_1020_);
lean_dec(v_x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1043_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_before_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1041_; 
v_before_1025_ = lean_ctor_get(v_head_1020_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_head_1020_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_head_1020_, 1);
lean_dec(v_unused_1042_);
v___x_1027_ = v_head_1020_;
v_isShared_1028_ = v_isSharedCheck_1041_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_before_1025_);
lean_dec(v_head_1020_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1041_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 7);
lean_ctor_set(v___x_1027_, 1, v___x_1029_);
lean_ctor_set(v___x_1027_, 0, v_x_1018_);
v___x_1031_ = v___x_1027_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_x_1018_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 7);
lean_ctor_set(v___x_1023_, 1, v___x_1032_);
lean_ctor_set(v___x_1023_, 0, v___x_1031_);
v___x_1034_ = v___x_1023_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1035_ = l_Lean_MessageData_ofSyntax(v_before_1025_);
v___x_1036_ = l_Lean_indentD(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v_x_1018_ = v___x_1037_;
v_x_1019_ = v_tail_1021_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object* v_opts_1044_, lean_object* v_opt_1045_){
_start:
{
lean_object* v_name_1046_; lean_object* v_defValue_1047_; lean_object* v_map_1048_; lean_object* v___x_1049_; 
v_name_1046_ = lean_ctor_get(v_opt_1045_, 0);
v_defValue_1047_ = lean_ctor_get(v_opt_1045_, 1);
v_map_1048_ = lean_ctor_get(v_opts_1044_, 0);
v___x_1049_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1048_, v_name_1046_);
if (lean_obj_tag(v___x_1049_) == 0)
{
uint8_t v___x_1050_; 
v___x_1050_ = lean_unbox(v_defValue_1047_);
return v___x_1050_;
}
else
{
lean_object* v_val_1051_; 
v_val_1051_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_val_1051_);
lean_dec_ref(v___x_1049_);
if (lean_obj_tag(v_val_1051_) == 1)
{
uint8_t v_v_1052_; 
v_v_1052_ = lean_ctor_get_uint8(v_val_1051_, 0);
lean_dec_ref(v_val_1051_);
return v_v_1052_;
}
else
{
uint8_t v___x_1053_; 
lean_dec(v_val_1051_);
v___x_1053_ = lean_unbox(v_defValue_1047_);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_opts_1054_, lean_object* v_opt_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_opts_1054_, v_opt_1055_);
lean_dec_ref(v_opt_1055_);
lean_dec_ref(v_opts_1054_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1));
v___x_1062_ = l_Lean_MessageData_ofFormat(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_1063_, lean_object* v_macroStack_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_options_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_options_1067_ = lean_ctor_get(v___y_1065_, 2);
v___x_1068_ = l_Lean_Elab_pp_macroStack;
v___x_1069_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
lean_dec(v_macroStack_1064_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_msgData_1063_);
return v___x_1070_;
}
else
{
if (lean_obj_tag(v_macroStack_1064_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_msgData_1063_);
return v___x_1071_;
}
else
{
lean_object* v_head_1072_; lean_object* v_after_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1088_; 
v_head_1072_ = lean_ctor_get(v_macroStack_1064_, 0);
lean_inc(v_head_1072_);
v_after_1073_ = lean_ctor_get(v_head_1072_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_head_1072_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v_head_1072_, 0);
lean_dec(v_unused_1089_);
v___x_1075_ = v_head_1072_;
v_isShared_1076_ = v_isSharedCheck_1088_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_after_1073_);
lean_dec(v_head_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1088_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1077_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 7);
lean_ctor_set(v___x_1075_, 1, v___x_1077_);
lean_ctor_set(v___x_1075_, 0, v_msgData_1063_);
v___x_1079_ = v___x_1075_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_msgData_1063_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_msgData_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1080_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofSyntax(v_after_1073_);
v___x_1083_ = l_Lean_indentD(v___x_1082_);
v_msgData_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1084_, 0, v___x_1081_);
lean_ctor_set(v_msgData_1084_, 1, v___x_1083_);
v___x_1085_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(v_msgData_1084_, v_macroStack_1064_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1090_, lean_object* v_macroStack_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1090_, v_macroStack_1091_, v___y_1092_);
lean_dec_ref(v___y_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v_env_1102_; lean_object* v___x_1103_; lean_object* v_mctx_1104_; lean_object* v_lctx_1105_; lean_object* v_options_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1101_ = lean_st_ref_get(v___y_1099_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
v___x_1103_ = lean_st_ref_get(v___y_1097_);
v_mctx_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc_ref(v_mctx_1104_);
lean_dec(v___x_1103_);
v_lctx_1105_ = lean_ctor_get(v___y_1096_, 2);
v_options_1106_ = lean_ctor_get(v___y_1098_, 2);
lean_inc_ref(v_options_1106_);
lean_inc_ref(v_lctx_1105_);
v___x_1107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1107_, 0, v_env_1102_);
lean_ctor_set(v___x_1107_, 1, v_mctx_1104_);
lean_ctor_set(v___x_1107_, 2, v_lctx_1105_);
lean_ctor_set(v___x_1107_, 3, v_options_1106_);
v___x_1108_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_msgData_1095_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_ref_1125_; lean_object* v___x_1126_; lean_object* v_a_1127_; lean_object* v_macroStack_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_ref_1125_ = lean_ctor_get(v___y_1122_, 5);
v___x_1126_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msg_1117_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v_macroStack_1128_ = lean_ctor_get(v___y_1118_, 1);
v___x_1129_ = l_Lean_Elab_getBetterRef(v_ref_1125_, v_macroStack_1128_);
lean_inc(v_macroStack_1128_);
v___x_1130_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_a_1127_, v_macroStack_1128_, v___y_1122_);
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1129_);
lean_ctor_set(v___x_1135_, 1, v_a_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_fileName_1158_; lean_object* v_fileMap_1159_; lean_object* v_options_1160_; lean_object* v_currRecDepth_1161_; lean_object* v_maxRecDepth_1162_; lean_object* v_ref_1163_; lean_object* v_currNamespace_1164_; lean_object* v_openDecls_1165_; lean_object* v_initHeartbeats_1166_; lean_object* v_maxHeartbeats_1167_; lean_object* v_quotContext_1168_; lean_object* v_currMacroScope_1169_; uint8_t v_diag_1170_; lean_object* v_cancelTk_x3f_1171_; uint8_t v_suppressElabErrors_1172_; lean_object* v_inheritedTraceOptions_1173_; lean_object* v_ref_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_fileName_1158_ = lean_ctor_get(v___y_1155_, 0);
v_fileMap_1159_ = lean_ctor_get(v___y_1155_, 1);
v_options_1160_ = lean_ctor_get(v___y_1155_, 2);
v_currRecDepth_1161_ = lean_ctor_get(v___y_1155_, 3);
v_maxRecDepth_1162_ = lean_ctor_get(v___y_1155_, 4);
v_ref_1163_ = lean_ctor_get(v___y_1155_, 5);
v_currNamespace_1164_ = lean_ctor_get(v___y_1155_, 6);
v_openDecls_1165_ = lean_ctor_get(v___y_1155_, 7);
v_initHeartbeats_1166_ = lean_ctor_get(v___y_1155_, 8);
v_maxHeartbeats_1167_ = lean_ctor_get(v___y_1155_, 9);
v_quotContext_1168_ = lean_ctor_get(v___y_1155_, 10);
v_currMacroScope_1169_ = lean_ctor_get(v___y_1155_, 11);
v_diag_1170_ = lean_ctor_get_uint8(v___y_1155_, sizeof(void*)*14);
v_cancelTk_x3f_1171_ = lean_ctor_get(v___y_1155_, 12);
v_suppressElabErrors_1172_ = lean_ctor_get_uint8(v___y_1155_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1173_ = lean_ctor_get(v___y_1155_, 13);
v_ref_1174_ = l_Lean_replaceRef(v_ref_1149_, v_ref_1163_);
lean_inc_ref(v_inheritedTraceOptions_1173_);
lean_inc(v_cancelTk_x3f_1171_);
lean_inc(v_currMacroScope_1169_);
lean_inc(v_quotContext_1168_);
lean_inc(v_maxHeartbeats_1167_);
lean_inc(v_initHeartbeats_1166_);
lean_inc(v_openDecls_1165_);
lean_inc(v_currNamespace_1164_);
lean_inc(v_maxRecDepth_1162_);
lean_inc(v_currRecDepth_1161_);
lean_inc_ref(v_options_1160_);
lean_inc_ref(v_fileMap_1159_);
lean_inc_ref(v_fileName_1158_);
v___x_1175_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1175_, 0, v_fileName_1158_);
lean_ctor_set(v___x_1175_, 1, v_fileMap_1159_);
lean_ctor_set(v___x_1175_, 2, v_options_1160_);
lean_ctor_set(v___x_1175_, 3, v_currRecDepth_1161_);
lean_ctor_set(v___x_1175_, 4, v_maxRecDepth_1162_);
lean_ctor_set(v___x_1175_, 5, v_ref_1174_);
lean_ctor_set(v___x_1175_, 6, v_currNamespace_1164_);
lean_ctor_set(v___x_1175_, 7, v_openDecls_1165_);
lean_ctor_set(v___x_1175_, 8, v_initHeartbeats_1166_);
lean_ctor_set(v___x_1175_, 9, v_maxHeartbeats_1167_);
lean_ctor_set(v___x_1175_, 10, v_quotContext_1168_);
lean_ctor_set(v___x_1175_, 11, v_currMacroScope_1169_);
lean_ctor_set(v___x_1175_, 12, v_cancelTk_x3f_1171_);
lean_ctor_set(v___x_1175_, 13, v_inheritedTraceOptions_1173_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*14, v_diag_1170_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*14 + 1, v_suppressElabErrors_1172_);
v___x_1176_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___x_1175_, v___y_1156_);
lean_dec_ref(v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1177_, lean_object* v_msg_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1177_, v_msg_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v_ref_1177_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___y_1199_; lean_object* v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; uint8_t v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; uint8_t v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; uint8_t v___y_1299_; uint8_t v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
lean_inc(v_docComment_1187_);
v___x_1360_ = l_Lean_Syntax_getKind(v_docComment_1187_);
v___x_1361_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_1362_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_1363_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_1364_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_1365_ = lean_name_eq(v___x_1360_, v___x_1364_);
lean_dec(v___x_1360_);
if (v___x_1365_ == 0)
{
goto v___jp_1337_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = l_Lean_Syntax_getArg(v_docComment_1187_, v___x_1366_);
if (lean_obj_tag(v___x_1367_) == 1)
{
lean_object* v_kind_1368_; 
v_kind_1368_ = lean_ctor_get(v___x_1367_, 1);
lean_inc(v_kind_1368_);
if (lean_obj_tag(v_kind_1368_) == 1)
{
lean_object* v_pre_1369_; 
v_pre_1369_ = lean_ctor_get(v_kind_1368_, 0);
lean_inc(v_pre_1369_);
if (lean_obj_tag(v_pre_1369_) == 1)
{
lean_object* v_pre_1370_; 
v_pre_1370_ = lean_ctor_get(v_pre_1369_, 0);
lean_inc(v_pre_1370_);
if (lean_obj_tag(v_pre_1370_) == 1)
{
lean_object* v_pre_1371_; 
v_pre_1371_ = lean_ctor_get(v_pre_1370_, 0);
lean_inc(v_pre_1371_);
if (lean_obj_tag(v_pre_1371_) == 1)
{
lean_object* v_pre_1372_; 
v_pre_1372_ = lean_ctor_get(v_pre_1371_, 0);
lean_inc(v_pre_1372_);
if (lean_obj_tag(v_pre_1372_) == 0)
{
lean_object* v_info_1373_; lean_object* v_args_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1400_; 
v_info_1373_ = lean_ctor_get(v___x_1367_, 0);
v_args_1374_ = lean_ctor_get(v___x_1367_, 2);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1367_, 1);
lean_dec(v_unused_1401_);
v___x_1376_ = v___x_1367_;
v_isShared_1377_ = v_isSharedCheck_1400_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_args_1374_);
lean_inc(v_info_1373_);
lean_dec(v___x_1367_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1400_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_str_1378_; lean_object* v_str_1379_; lean_object* v_str_1380_; lean_object* v_str_1381_; uint8_t v___x_1382_; 
v_str_1378_ = lean_ctor_get(v_kind_1368_, 1);
lean_inc_ref(v_str_1378_);
lean_dec_ref(v_kind_1368_);
v_str_1379_ = lean_ctor_get(v_pre_1369_, 1);
lean_inc_ref(v_str_1379_);
lean_dec_ref(v_pre_1369_);
v_str_1380_ = lean_ctor_get(v_pre_1370_, 1);
lean_inc_ref(v_str_1380_);
lean_dec_ref(v_pre_1370_);
v_str_1381_ = lean_ctor_get(v_pre_1371_, 1);
lean_inc_ref(v_str_1381_);
lean_dec_ref(v_pre_1371_);
v___x_1382_ = lean_string_dec_eq(v_str_1381_, v___x_1361_);
lean_dec_ref(v_str_1381_);
if (v___x_1382_ == 0)
{
lean_dec_ref(v_str_1380_);
lean_dec_ref(v_str_1379_);
lean_dec_ref(v_str_1378_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_args_1374_);
lean_dec(v_info_1373_);
goto v___jp_1337_;
}
else
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_string_dec_eq(v_str_1380_, v___x_1362_);
lean_dec_ref(v_str_1380_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_str_1379_);
lean_dec_ref(v_str_1378_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_args_1374_);
lean_dec(v_info_1373_);
goto v___jp_1337_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_string_dec_eq(v_str_1379_, v___x_1363_);
lean_dec_ref(v_str_1379_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v_str_1378_);
lean_del_object(v___x_1376_);
lean_dec_ref(v_args_1374_);
lean_dec(v_info_1373_);
goto v___jp_1337_;
}
else
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_1386_ = lean_string_dec_eq(v_str_1378_, v___x_1385_);
lean_dec_ref(v_str_1378_);
if (v___x_1386_ == 0)
{
lean_del_object(v___x_1376_);
lean_dec_ref(v_args_1374_);
lean_dec(v_info_1373_);
goto v___jp_1337_;
}
else
{
lean_dec(v_docComment_1187_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_del_object(v___x_1376_);
lean_dec_ref(v_args_1374_);
lean_dec(v_info_1373_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1389_ = l_Lean_Name_str___override(v_pre_1372_, v___x_1361_);
v___x_1390_ = l_Lean_Name_str___override(v___x_1389_, v___x_1362_);
v___x_1391_ = l_Lean_Name_str___override(v___x_1390_, v___x_1363_);
v___x_1392_ = l_Lean_Name_str___override(v___x_1391_, v___x_1385_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v___x_1392_);
v___x_1394_ = v___x_1376_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_info_1373_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_args_1374_);
v___x_1394_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = l_Lean_Syntax_getArg(v___x_1394_, v___x_1395_);
lean_dec_ref(v___x_1394_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_1372_);
lean_dec_ref(v_pre_1371_);
lean_dec_ref(v_pre_1370_);
lean_dec_ref(v_pre_1369_);
lean_dec_ref(v_kind_1368_);
lean_dec_ref(v___x_1367_);
goto v___jp_1337_;
}
}
else
{
lean_dec_ref(v_pre_1370_);
lean_dec(v_pre_1371_);
lean_dec_ref(v_pre_1369_);
lean_dec_ref(v_kind_1368_);
lean_dec_ref(v___x_1367_);
goto v___jp_1337_;
}
}
else
{
lean_dec_ref(v_pre_1369_);
lean_dec(v_pre_1370_);
lean_dec_ref(v_kind_1368_);
lean_dec_ref(v___x_1367_);
goto v___jp_1337_;
}
}
else
{
lean_dec(v_pre_1369_);
lean_dec_ref(v_kind_1368_);
lean_dec_ref(v___x_1367_);
goto v___jp_1337_;
}
}
else
{
lean_dec_ref(v___x_1367_);
lean_dec(v_kind_1368_);
goto v___jp_1337_;
}
}
else
{
lean_dec(v___x_1367_);
goto v___jp_1337_;
}
}
v___jp_1195_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
v___jp_1198_:
{
lean_object* v___x_1208_; lean_object* v_currNamespace_1209_; lean_object* v_openDecls_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_env_1214_; lean_object* v_nextMacroScope_1215_; lean_object* v_ngen_1216_; lean_object* v_auxDeclNGen_1217_; lean_object* v_traceState_1218_; lean_object* v_cache_1219_; lean_object* v_messages_1220_; lean_object* v_infoState_1221_; lean_object* v_snapshotTasks_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1231_; 
v___x_1208_ = lean_st_ref_take(v___y_1207_);
v_currNamespace_1209_ = lean_ctor_get(v___y_1206_, 6);
v_openDecls_1210_ = lean_ctor_get(v___y_1206_, 7);
lean_inc(v_openDecls_1210_);
lean_inc(v_currNamespace_1209_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_currNamespace_1209_);
lean_ctor_set(v___x_1211_, 1, v_openDecls_1210_);
v___x_1212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v___y_1199_);
lean_inc(v___y_1204_);
lean_inc_ref(v___y_1202_);
v___x_1213_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1213_, 0, v___y_1202_);
lean_ctor_set(v___x_1213_, 1, v___y_1205_);
lean_ctor_set(v___x_1213_, 2, v___y_1204_);
lean_ctor_set(v___x_1213_, 3, v___y_1200_);
lean_ctor_set(v___x_1213_, 4, v___x_1212_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*5, v___y_1203_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*5 + 1, v___y_1201_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*5 + 2, v___y_1203_);
v_env_1214_ = lean_ctor_get(v___x_1208_, 0);
v_nextMacroScope_1215_ = lean_ctor_get(v___x_1208_, 1);
v_ngen_1216_ = lean_ctor_get(v___x_1208_, 2);
v_auxDeclNGen_1217_ = lean_ctor_get(v___x_1208_, 3);
v_traceState_1218_ = lean_ctor_get(v___x_1208_, 4);
v_cache_1219_ = lean_ctor_get(v___x_1208_, 5);
v_messages_1220_ = lean_ctor_get(v___x_1208_, 6);
v_infoState_1221_ = lean_ctor_get(v___x_1208_, 7);
v_snapshotTasks_1222_ = lean_ctor_get(v___x_1208_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1224_ = v___x_1208_;
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snapshotTasks_1222_);
lean_inc(v_infoState_1221_);
lean_inc(v_messages_1220_);
lean_inc(v_cache_1219_);
lean_inc(v_traceState_1218_);
lean_inc(v_auxDeclNGen_1217_);
lean_inc(v_ngen_1216_);
lean_inc(v_nextMacroScope_1215_);
lean_inc(v_env_1214_);
lean_dec(v___x_1208_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1231_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = l_Lean_MessageLog_add(v___x_1213_, v_messages_1220_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 6, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_env_1214_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_nextMacroScope_1215_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_ngen_1216_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_auxDeclNGen_1217_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_traceState_1218_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v_cache_1219_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_infoState_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_snapshotTasks_1222_);
v___x_1228_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_st_ref_set(v___y_1207_, v___x_1228_);
goto v___jp_1195_;
}
}
}
v___jp_1232_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
lean_inc_ref(v___y_1239_);
v___x_1240_ = l_Lean_Parser_ParserState_allErrors(v___y_1239_);
v___x_1241_ = lean_array_get_size(v___x_1240_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_nat_dec_eq(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1236_);
v___x_1244_ = lean_box(0);
v_sz_1245_ = lean_array_size(v___x_1240_);
v___x_1246_ = ((size_t)0ULL);
lean_inc_ref(v___y_1237_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1237_, v___x_1241_, v___x_1240_, v_sz_1245_, v___x_1246_, v___x_1244_, v___y_1192_, v___y_1193_);
lean_dec_ref(v___x_1240_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1255_; 
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1256_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1247_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1247_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_stxStack_1265_; lean_object* v_pos_1266_; uint8_t v___x_1267_; 
lean_dec_ref(v___x_1240_);
v_stxStack_1265_ = lean_ctor_get(v___y_1239_, 0);
lean_inc_ref(v_stxStack_1265_);
v_pos_1266_ = lean_ctor_get(v___y_1239_, 2);
lean_inc(v_pos_1266_);
lean_dec_ref(v___y_1239_);
v___x_1267_ = l_Lean_Parser_InputContext_atEnd(v___y_1236_, v_pos_1266_);
lean_dec_ref(v___y_1236_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint32_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref(v_stxStack_1265_);
lean_inc_ref(v___y_1237_);
v___x_1268_ = l_Lean_FileMap_toPosition(v___y_1237_, v_pos_1266_);
v___x_1269_ = lean_box(0);
v___x_1270_ = 2;
v___x_1271_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1272_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1273_ = lean_string_utf8_get(v___y_1238_, v_pos_1266_);
lean_dec(v_pos_1266_);
v___x_1274_ = lean_string_push(v___x_1271_, v___x_1273_);
v___x_1275_ = lean_string_append(v___x_1272_, v___x_1274_);
lean_dec_ref(v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1277_ = lean_string_append(v___x_1275_, v___x_1276_);
v___x_1278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = l_Lean_MessageData_ofFormat(v___x_1278_);
if (v___y_1234_ == 0)
{
v___y_1199_ = v___x_1279_;
v___y_1200_ = v___x_1271_;
v___y_1201_ = v___x_1270_;
v___y_1202_ = v___y_1235_;
v___y_1203_ = v___x_1267_;
v___y_1204_ = v___x_1269_;
v___y_1205_ = v___x_1268_;
v___y_1206_ = v___y_1192_;
v___y_1207_ = v___y_1193_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___f_1282_; uint8_t v___x_1283_; 
v___x_1280_ = lean_box(v___x_1267_);
v___x_1281_ = lean_box(v___y_1233_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1282_, 0, v___x_1280_);
lean_closure_set(v___f_1282_, 1, v___x_1281_);
lean_inc_ref(v___x_1279_);
v___x_1283_ = l_Lean_MessageData_hasTag(v___f_1282_, v___x_1279_);
if (v___x_1283_ == 0)
{
lean_dec_ref(v___x_1279_);
lean_dec_ref(v___x_1268_);
goto v___jp_1195_;
}
else
{
v___y_1199_ = v___x_1279_;
v___y_1200_ = v___x_1271_;
v___y_1201_ = v___x_1270_;
v___y_1202_ = v___y_1235_;
v___y_1203_ = v___x_1267_;
v___y_1204_ = v___x_1269_;
v___y_1205_ = v___x_1268_;
v___y_1206_ = v___y_1192_;
v___y_1207_ = v___y_1193_;
goto v___jp_1198_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_pos_1266_);
v___x_1284_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1265_);
lean_dec_ref(v_stxStack_1265_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
v___jp_1287_:
{
if (v___y_1299_ == 0)
{
lean_dec_ref(v___y_1295_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
v___y_1233_ = v___y_1288_;
v___y_1234_ = v___y_1292_;
v___y_1235_ = v___y_1294_;
v___y_1236_ = v___y_1296_;
v___y_1237_ = v___y_1297_;
v___y_1238_ = v___y_1298_;
v___y_1239_ = v___y_1291_;
goto v___jp_1232_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v_pos_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___y_1290_);
lean_ctor_set(v___x_1303_, 1, v___x_1300_);
v___x_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1300_);
lean_ctor_set(v___x_1304_, 1, v___x_1301_);
lean_ctor_set(v___x_1304_, 2, v___x_1302_);
lean_ctor_set(v___x_1304_, 3, v___x_1303_);
lean_ctor_set(v___x_1304_, 4, v___x_1300_);
v_pos_1305_ = lean_ctor_get(v___y_1291_, 2);
lean_inc(v_pos_1305_);
lean_dec_ref(v___y_1291_);
v___x_1306_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_1306_, 0, v___x_1304_);
v___x_1307_ = l_Lean_Parser_ParserState_setPos(v___y_1293_, v_pos_1305_);
lean_inc_ref(v___y_1296_);
v___x_1308_ = l_Lean_Parser_ParserFn_run(v___x_1306_, v___y_1296_, v___y_1295_, v___y_1289_, v___x_1307_);
v___y_1233_ = v___y_1288_;
v___y_1234_ = v___y_1292_;
v___y_1235_ = v___y_1294_;
v___y_1236_ = v___y_1296_;
v___y_1237_ = v___y_1297_;
v___y_1238_ = v___y_1298_;
v___y_1239_ = v___x_1308_;
goto v___jp_1232_;
}
}
v___jp_1309_:
{
lean_object* v___x_1321_; lean_object* v_env_1322_; lean_object* v_ictx_1323_; lean_object* v_pmctx_1324_; lean_object* v_blockCtxt_1325_; lean_object* v___x_1326_; lean_object* v_s_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v_s_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1321_ = lean_st_ref_get(v___y_1193_);
v_env_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref_n(v_env_1322_, 2);
lean_dec(v___x_1321_);
lean_inc(v___y_1320_);
lean_inc_ref_n(v___y_1318_, 2);
lean_inc_ref(v___y_1317_);
lean_inc_ref(v___y_1311_);
v_ictx_1323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1323_, 0, v___y_1311_);
lean_ctor_set(v_ictx_1323_, 1, v___y_1317_);
lean_ctor_set(v_ictx_1323_, 2, v___y_1318_);
lean_ctor_set(v_ictx_1323_, 3, v___y_1320_);
lean_inc(v___y_1319_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1316_);
v_pmctx_1324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1324_, 0, v_env_1322_);
lean_ctor_set(v_pmctx_1324_, 1, v___y_1316_);
lean_ctor_set(v_pmctx_1324_, 2, v___y_1314_);
lean_ctor_set(v_pmctx_1324_, 3, v___y_1319_);
lean_inc(v___y_1312_);
v_blockCtxt_1325_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1318_, v___y_1312_, v___y_1320_);
v___x_1326_ = l_Lean_Parser_mkParserState(v___y_1311_);
lean_inc_ref(v___x_1326_);
v_s_1327_ = l_Lean_Parser_ParserState_setPos(v___x_1326_, v___y_1312_);
v___x_1328_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_1328_, 0, v_blockCtxt_1325_);
v___x_1329_ = l_Lean_Parser_getTokenTable(v_env_1322_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v_pmctx_1324_);
lean_inc_ref(v_ictx_1323_);
v_s_1330_ = l_Lean_Parser_ParserFn_run(v___x_1328_, v_ictx_1323_, v_pmctx_1324_, v___x_1329_, v_s_1327_);
lean_inc_ref(v_s_1330_);
v___x_1331_ = l_Lean_Parser_ParserState_allErrors(v_s_1330_);
v___x_1332_ = lean_array_get_size(v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(0u);
v___x_1334_ = lean_nat_dec_eq(v___x_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
v___y_1288_ = v___y_1310_;
v___y_1289_ = v___x_1329_;
v___y_1290_ = v___y_1313_;
v___y_1291_ = v_s_1330_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v___x_1326_;
v___y_1294_ = v___y_1317_;
v___y_1295_ = v_pmctx_1324_;
v___y_1296_ = v_ictx_1323_;
v___y_1297_ = v___y_1318_;
v___y_1298_ = v___y_1311_;
v___y_1299_ = v___x_1334_;
goto v___jp_1287_;
}
else
{
lean_object* v_pos_1335_; uint8_t v___x_1336_; 
v_pos_1335_ = lean_ctor_get(v_s_1330_, 2);
lean_inc(v_pos_1335_);
v___x_1336_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1323_, v_pos_1335_);
lean_dec(v_pos_1335_);
if (v___x_1336_ == 0)
{
v___y_1288_ = v___y_1310_;
v___y_1289_ = v___x_1329_;
v___y_1290_ = v___y_1313_;
v___y_1291_ = v_s_1330_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v___x_1326_;
v___y_1294_ = v___y_1317_;
v___y_1295_ = v_pmctx_1324_;
v___y_1296_ = v_ictx_1323_;
v___y_1297_ = v___y_1318_;
v___y_1298_ = v___y_1311_;
v___y_1299_ = v___x_1334_;
goto v___jp_1287_;
}
else
{
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1326_);
lean_dec_ref(v_pmctx_1324_);
lean_dec(v___y_1313_);
v___y_1233_ = v___y_1310_;
v___y_1234_ = v___y_1315_;
v___y_1235_ = v___y_1317_;
v___y_1236_ = v_ictx_1323_;
v___y_1237_ = v___y_1318_;
v___y_1238_ = v___y_1311_;
v___y_1239_ = v_s_1330_;
goto v___jp_1232_;
}
}
}
v___jp_1337_:
{
lean_object* v_fileName_1338_; lean_object* v_fileMap_1339_; lean_object* v_options_1340_; lean_object* v_currNamespace_1341_; lean_object* v_openDecls_1342_; uint8_t v_suppressElabErrors_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v_fileName_1338_ = lean_ctor_get(v___y_1192_, 0);
v_fileMap_1339_ = lean_ctor_get(v___y_1192_, 1);
v_options_1340_ = lean_ctor_get(v___y_1192_, 2);
v_currNamespace_1341_ = lean_ctor_get(v___y_1192_, 6);
v_openDecls_1342_ = lean_ctor_get(v___y_1192_, 7);
v_suppressElabErrors_1343_ = lean_ctor_get_uint8(v___y_1192_, sizeof(void*)*14 + 1);
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = l_Lean_Syntax_getArg(v_docComment_1187_, v___x_1344_);
v___x_1346_ = 1;
v___x_1347_ = l_Lean_Syntax_getPos_x3f(v___x_1345_, v___x_1346_);
if (lean_obj_tag(v___x_1347_) == 1)
{
lean_object* v_val_1348_; lean_object* v___x_1349_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = l_Lean_Syntax_getTailPos_x3f(v___x_1345_, v___x_1346_);
lean_dec(v___x_1345_);
if (lean_obj_tag(v___x_1349_) == 1)
{
lean_object* v_val_1350_; lean_object* v_source_1351_; lean_object* v___x_1352_; lean_object* v_endPos_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
lean_dec(v_docComment_1187_);
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref(v___x_1349_);
v_source_1351_ = lean_ctor_get(v_fileMap_1339_, 0);
v___x_1352_ = lean_string_utf8_prev(v_source_1351_, v_val_1350_);
lean_dec(v_val_1350_);
v_endPos_1353_ = lean_string_utf8_prev(v_source_1351_, v___x_1352_);
lean_dec(v___x_1352_);
v___x_1354_ = lean_string_utf8_byte_size(v_source_1351_);
v___x_1355_ = lean_nat_dec_le(v_endPos_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec(v_endPos_1353_);
v___y_1310_ = v_suppressElabErrors_1343_;
v___y_1311_ = v_source_1351_;
v___y_1312_ = v_val_1348_;
v___y_1313_ = v___x_1344_;
v___y_1314_ = v_currNamespace_1341_;
v___y_1315_ = v_suppressElabErrors_1343_;
v___y_1316_ = v_options_1340_;
v___y_1317_ = v_fileName_1338_;
v___y_1318_ = v_fileMap_1339_;
v___y_1319_ = v_openDecls_1342_;
v___y_1320_ = v___x_1354_;
goto v___jp_1309_;
}
else
{
v___y_1310_ = v_suppressElabErrors_1343_;
v___y_1311_ = v_source_1351_;
v___y_1312_ = v_val_1348_;
v___y_1313_ = v___x_1344_;
v___y_1314_ = v_currNamespace_1341_;
v___y_1315_ = v_suppressElabErrors_1343_;
v___y_1316_ = v_options_1340_;
v___y_1317_ = v_fileName_1338_;
v___y_1318_ = v_fileMap_1339_;
v___y_1319_ = v_openDecls_1342_;
v___y_1320_ = v_endPos_1353_;
goto v___jp_1309_;
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v___x_1349_);
lean_dec(v_val_1348_);
v___x_1356_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1357_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1187_, v___x_1356_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v_docComment_1187_);
return v___x_1357_;
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v___x_1347_);
lean_dec(v___x_1345_);
v___x_1358_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1359_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1187_, v___x_1358_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v_docComment_1187_);
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1415_, lean_object* v_binders_1416_, lean_object* v_docComment_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1442_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1442_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1442_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_a_1426_) == 1)
{
lean_object* v_val_1430_; lean_object* v___x_1431_; size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
lean_del_object(v___x_1428_);
v_val_1430_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_val_1430_);
lean_dec_ref(v_a_1426_);
v___x_1431_ = l_Lean_Syntax_getArgs(v_val_1430_);
lean_dec(v_val_1430_);
v_sz_1432_ = lean_array_size(v___x_1431_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_1432_, v___x_1433_, v___x_1431_);
v___x_1435_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1435_, 0, v___x_1434_);
v___x_1436_ = 0;
v___x_1437_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1415_, v_binders_1416_, v___x_1435_, v___x_1436_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec(v_a_1426_);
lean_dec(v_binders_1416_);
lean_dec(v_declName_1415_);
v___x_1438_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1438_);
v___x_1440_ = v___x_1428_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_binders_1416_);
lean_dec(v_declName_1415_);
v_a_1443_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1425_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1425_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1451_, lean_object* v_binders_1452_, lean_object* v_docComment_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_versoDocString(v_declName_1451_, v_binders_1452_, v_docComment_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_1462_, lean_object* v___x_1463_, lean_object* v_as_1464_, size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_b_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1462_, v___x_1463_, v_as_1464_, v_sz_1465_, v_i_1466_, v_b_1467_, v___y_1472_, v___y_1473_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v_as_1478_, lean_object* v_sz_1479_, lean_object* v_i_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
size_t v_sz_boxed_1489_; size_t v_i_boxed_1490_; lean_object* v_res_1491_; 
v_sz_boxed_1489_ = lean_unbox_usize(v_sz_1479_);
lean_dec(v_sz_1479_);
v_i_boxed_1490_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_res_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_1476_, v___x_1477_, v_as_1478_, v_sz_boxed_1489_, v_i_boxed_1490_, v_b_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec_ref(v_as_1478_);
lean_dec(v___x_1477_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_1492_, lean_object* v_ref_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1493_, v_msg_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_ref_1504_, lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_1503_, v_ref_1504_, v_msg_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v_ref_1504_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_msg_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_1524_, v_msg_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_1534_, lean_object* v_macroStack_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1534_, v_macroStack_1535_, v___y_1540_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_1544_, lean_object* v_macroStack_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_1544_, v_macroStack_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_bs_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1557_ == 0)
{
return v_bs_1556_;
}
else
{
lean_object* v_v_1558_; lean_object* v___x_1559_; lean_object* v_bs_x27_1560_; size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_v_1558_ = lean_array_uget(v_bs_1556_, v_i_1555_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v_bs_x27_1560_ = lean_array_uset(v_bs_1556_, v_i_1555_, v___x_1559_);
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_add(v_i_1555_, v___x_1561_);
v___x_1563_ = lean_array_uset(v_bs_x27_1560_, v_i_1555_, v_v_1558_);
v_i_1555_ = v___x_1562_;
v_bs_1556_ = v___x_1563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_bs_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1571_, lean_object* v_doc_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v___x_1580_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1588_; lean_object* v_env_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1580_ = lean_st_ref_get(v_a_1578_);
v_env_1595_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_env_1595_);
lean_dec(v___x_1580_);
v___x_1596_ = l_Lean_getMainVersoModuleDocs(v_env_1595_);
v___x_1597_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1596_);
lean_dec_ref(v___x_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
v___y_1588_ = v___x_1597_;
goto v___jp_1587_;
}
else
{
lean_object* v_val_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1607_; 
v_val_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_val_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_nat_add(v_val_1598_, v___x_1602_);
lean_dec(v_val_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
v___y_1588_ = v___x_1605_;
goto v___jp_1587_;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1584_; uint8_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1584_, 0, v_range_1571_);
lean_closure_set(v___x_1584_, 1, v___y_1582_);
lean_closure_set(v___x_1584_, 2, v___y_1583_);
v___x_1585_ = 0;
v___x_1586_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1584_, v___x_1585_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
return v___x_1586_;
}
v___jp_1587_:
{
lean_object* v___x_1589_; size_t v_sz_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1589_ = l_Lean_Syntax_getArgs(v_doc_1572_);
v_sz_1590_ = lean_array_size(v___x_1589_);
v___x_1591_ = ((size_t)0ULL);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_1590_, v___x_1591_, v___x_1589_);
if (lean_obj_tag(v___y_1588_) == 0)
{
lean_object* v___x_1593_; 
v___x_1593_ = lean_unsigned_to_nat(0u);
v___y_1582_ = v___x_1592_;
v___y_1583_ = v___x_1593_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1594_; 
v_val_1594_ = lean_ctor_get(v___y_1588_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v___y_1588_);
v___y_1582_ = v___x_1592_;
v___y_1583_ = v_val_1594_;
goto v___jp_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1608_, lean_object* v_doc_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_versoModDocString(v_range_1608_, v_doc_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_doc_1609_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object* v___x_1618_, lean_object* v_declName_1619_, lean_object* v___x_1620_, lean_object* v___x_1621_, uint8_t v___x_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_fileName_1630_; lean_object* v_options_1631_; lean_object* v_currRecDepth_1632_; lean_object* v_maxRecDepth_1633_; lean_object* v_ref_1634_; lean_object* v_currNamespace_1635_; lean_object* v_openDecls_1636_; lean_object* v_initHeartbeats_1637_; lean_object* v_maxHeartbeats_1638_; lean_object* v_quotContext_1639_; lean_object* v_currMacroScope_1640_; uint8_t v_diag_1641_; lean_object* v_cancelTk_x3f_1642_; uint8_t v_suppressElabErrors_1643_; lean_object* v_inheritedTraceOptions_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_fileName_1630_ = lean_ctor_get(v___y_1627_, 0);
v_options_1631_ = lean_ctor_get(v___y_1627_, 2);
v_currRecDepth_1632_ = lean_ctor_get(v___y_1627_, 3);
v_maxRecDepth_1633_ = lean_ctor_get(v___y_1627_, 4);
v_ref_1634_ = lean_ctor_get(v___y_1627_, 5);
v_currNamespace_1635_ = lean_ctor_get(v___y_1627_, 6);
v_openDecls_1636_ = lean_ctor_get(v___y_1627_, 7);
v_initHeartbeats_1637_ = lean_ctor_get(v___y_1627_, 8);
v_maxHeartbeats_1638_ = lean_ctor_get(v___y_1627_, 9);
v_quotContext_1639_ = lean_ctor_get(v___y_1627_, 10);
v_currMacroScope_1640_ = lean_ctor_get(v___y_1627_, 11);
v_diag_1641_ = lean_ctor_get_uint8(v___y_1627_, sizeof(void*)*14);
v_cancelTk_x3f_1642_ = lean_ctor_get(v___y_1627_, 12);
v_suppressElabErrors_1643_ = lean_ctor_get_uint8(v___y_1627_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1644_ = lean_ctor_get(v___y_1627_, 13);
lean_inc_ref(v_inheritedTraceOptions_1644_);
lean_inc(v_cancelTk_x3f_1642_);
lean_inc(v_currMacroScope_1640_);
lean_inc(v_quotContext_1639_);
lean_inc(v_maxHeartbeats_1638_);
lean_inc(v_initHeartbeats_1637_);
lean_inc(v_openDecls_1636_);
lean_inc(v_currNamespace_1635_);
lean_inc(v_ref_1634_);
lean_inc(v_maxRecDepth_1633_);
lean_inc(v_currRecDepth_1632_);
lean_inc_ref(v_options_1631_);
lean_inc_ref(v_fileName_1630_);
v___x_1645_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1645_, 0, v_fileName_1630_);
lean_ctor_set(v___x_1645_, 1, v___x_1618_);
lean_ctor_set(v___x_1645_, 2, v_options_1631_);
lean_ctor_set(v___x_1645_, 3, v_currRecDepth_1632_);
lean_ctor_set(v___x_1645_, 4, v_maxRecDepth_1633_);
lean_ctor_set(v___x_1645_, 5, v_ref_1634_);
lean_ctor_set(v___x_1645_, 6, v_currNamespace_1635_);
lean_ctor_set(v___x_1645_, 7, v_openDecls_1636_);
lean_ctor_set(v___x_1645_, 8, v_initHeartbeats_1637_);
lean_ctor_set(v___x_1645_, 9, v_maxHeartbeats_1638_);
lean_ctor_set(v___x_1645_, 10, v_quotContext_1639_);
lean_ctor_set(v___x_1645_, 11, v_currMacroScope_1640_);
lean_ctor_set(v___x_1645_, 12, v_cancelTk_x3f_1642_);
lean_ctor_set(v___x_1645_, 13, v_inheritedTraceOptions_1644_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*14, v_diag_1641_);
lean_ctor_set_uint8(v___x_1645_, sizeof(void*)*14 + 1, v_suppressElabErrors_1643_);
v___x_1646_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1619_, v___x_1620_, v___x_1621_, v___x_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___x_1645_, v___y_1628_);
lean_dec_ref(v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object* v___x_1647_, lean_object* v_declName_1648_, lean_object* v___x_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v___x_15596__boxed_1659_; lean_object* v_res_1660_; 
v___x_15596__boxed_1659_ = lean_unbox(v___x_1651_);
v_res_1660_ = l_Lean_versoDocStringFromString___lam__0(v___x_1647_, v_declName_1648_, v___x_1649_, v___x_1650_, v___x_15596__boxed_1659_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t v___y_1661_, uint8_t v_suppressElabErrors_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 1)
{
lean_object* v_pre_1664_; 
v_pre_1664_ = lean_ctor_get(v_x_1663_, 0);
switch(lean_obj_tag(v_pre_1664_))
{
case 1:
{
lean_object* v_pre_1665_; 
v_pre_1665_ = lean_ctor_get(v_pre_1664_, 0);
switch(lean_obj_tag(v_pre_1665_))
{
case 0:
{
lean_object* v_str_1666_; lean_object* v_str_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_str_1666_ = lean_ctor_get(v_x_1663_, 1);
v_str_1667_ = lean_ctor_get(v_pre_1664_, 1);
v___x_1668_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_1669_ = lean_string_dec_eq(v_str_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_1671_ = lean_string_dec_eq(v_str_1667_, v___x_1670_);
if (v___x_1671_ == 0)
{
return v___y_1661_;
}
else
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_1673_ = lean_string_dec_eq(v_str_1666_, v___x_1672_);
if (v___x_1673_ == 0)
{
return v___y_1661_;
}
else
{
return v_suppressElabErrors_1662_;
}
}
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_1675_ = lean_string_dec_eq(v_str_1666_, v___x_1674_);
if (v___x_1675_ == 0)
{
return v___y_1661_;
}
else
{
return v_suppressElabErrors_1662_;
}
}
}
case 1:
{
lean_object* v_pre_1676_; 
v_pre_1676_ = lean_ctor_get(v_pre_1665_, 0);
if (lean_obj_tag(v_pre_1676_) == 0)
{
lean_object* v_str_1677_; lean_object* v_str_1678_; lean_object* v_str_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_str_1677_ = lean_ctor_get(v_x_1663_, 1);
v_str_1678_ = lean_ctor_get(v_pre_1664_, 1);
v_str_1679_ = lean_ctor_get(v_pre_1665_, 1);
v___x_1680_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_1681_ = lean_string_dec_eq(v_str_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
return v___y_1661_;
}
else
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_1683_ = lean_string_dec_eq(v_str_1678_, v___x_1682_);
if (v___x_1683_ == 0)
{
return v___y_1661_;
}
else
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_1685_ = lean_string_dec_eq(v_str_1677_, v___x_1684_);
if (v___x_1685_ == 0)
{
return v___y_1661_;
}
else
{
return v_suppressElabErrors_1662_;
}
}
}
}
else
{
return v___y_1661_;
}
}
default: 
{
return v___y_1661_;
}
}
}
case 0:
{
lean_object* v_str_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_str_1686_ = lean_ctor_get(v_x_1663_, 1);
v___x_1687_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_1688_ = lean_string_dec_eq(v_str_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
return v___y_1661_;
}
else
{
return v_suppressElabErrors_1662_;
}
}
default: 
{
return v___y_1661_;
}
}
}
else
{
return v___y_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object* v___y_1689_, lean_object* v_suppressElabErrors_1690_, lean_object* v_x_1691_){
_start:
{
uint8_t v___y_15638__boxed_1692_; uint8_t v_suppressElabErrors_boxed_1693_; uint8_t v_res_1694_; lean_object* v_r_1695_; 
v___y_15638__boxed_1692_ = lean_unbox(v___y_1689_);
v_suppressElabErrors_boxed_1693_ = lean_unbox(v_suppressElabErrors_1690_);
v_res_1694_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(v___y_15638__boxed_1692_, v_suppressElabErrors_boxed_1693_, v_x_1691_);
lean_dec(v_x_1691_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object* v_ref_1696_, lean_object* v_msgData_1697_, uint8_t v_severity_1698_, uint8_t v_isSilent_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v___y_1706_; uint8_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1742_; uint8_t v___y_1743_; uint8_t v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1767_; uint8_t v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1778_; uint8_t v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; uint8_t v___y_1783_; uint8_t v___y_1784_; uint8_t v___x_1789_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; uint8_t v___y_1795_; uint8_t v___y_1796_; uint8_t v___y_1797_; uint8_t v___y_1799_; uint8_t v___x_1814_; 
v___x_1789_ = 2;
v___x_1814_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1698_, v___x_1789_);
if (v___x_1814_ == 0)
{
v___y_1799_ = v___x_1814_;
goto v___jp_1798_;
}
else
{
uint8_t v___x_1815_; 
lean_inc_ref(v_msgData_1697_);
v___x_1815_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1697_);
v___y_1799_ = v___x_1815_;
goto v___jp_1798_;
}
v___jp_1705_:
{
lean_object* v___x_1715_; lean_object* v_currNamespace_1716_; lean_object* v_openDecls_1717_; lean_object* v_env_1718_; lean_object* v_nextMacroScope_1719_; lean_object* v_ngen_1720_; lean_object* v_auxDeclNGen_1721_; lean_object* v_traceState_1722_; lean_object* v_cache_1723_; lean_object* v_messages_1724_; lean_object* v_infoState_1725_; lean_object* v_snapshotTasks_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1740_; 
v___x_1715_ = lean_st_ref_take(v___y_1714_);
v_currNamespace_1716_ = lean_ctor_get(v___y_1713_, 6);
v_openDecls_1717_ = lean_ctor_get(v___y_1713_, 7);
v_env_1718_ = lean_ctor_get(v___x_1715_, 0);
v_nextMacroScope_1719_ = lean_ctor_get(v___x_1715_, 1);
v_ngen_1720_ = lean_ctor_get(v___x_1715_, 2);
v_auxDeclNGen_1721_ = lean_ctor_get(v___x_1715_, 3);
v_traceState_1722_ = lean_ctor_get(v___x_1715_, 4);
v_cache_1723_ = lean_ctor_get(v___x_1715_, 5);
v_messages_1724_ = lean_ctor_get(v___x_1715_, 6);
v_infoState_1725_ = lean_ctor_get(v___x_1715_, 7);
v_snapshotTasks_1726_ = lean_ctor_get(v___x_1715_, 8);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1728_ = v___x_1715_;
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_snapshotTasks_1726_);
lean_inc(v_infoState_1725_);
lean_inc(v_messages_1724_);
lean_inc(v_cache_1723_);
lean_inc(v_traceState_1722_);
lean_inc(v_auxDeclNGen_1721_);
lean_inc(v_ngen_1720_);
lean_inc(v_nextMacroScope_1719_);
lean_inc(v_env_1718_);
lean_dec(v___x_1715_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1740_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
lean_inc(v_openDecls_1717_);
lean_inc(v_currNamespace_1716_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_currNamespace_1716_);
lean_ctor_set(v___x_1730_, 1, v_openDecls_1717_);
v___x_1731_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___y_1708_);
lean_inc_ref(v___y_1709_);
lean_inc_ref(v___y_1711_);
v___x_1732_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1732_, 0, v___y_1711_);
lean_ctor_set(v___x_1732_, 1, v___y_1710_);
lean_ctor_set(v___x_1732_, 2, v___y_1712_);
lean_ctor_set(v___x_1732_, 3, v___y_1709_);
lean_ctor_set(v___x_1732_, 4, v___x_1731_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*5, v___y_1707_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*5 + 1, v___y_1706_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*5 + 2, v_isSilent_1699_);
v___x_1733_ = l_Lean_MessageLog_add(v___x_1732_, v_messages_1724_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 6, v___x_1733_);
v___x_1735_ = v___x_1728_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_env_1718_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_nextMacroScope_1719_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_ngen_1720_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_auxDeclNGen_1721_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_traceState_1722_);
lean_ctor_set(v_reuseFailAlloc_1739_, 5, v_cache_1723_);
lean_ctor_set(v_reuseFailAlloc_1739_, 6, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1739_, 7, v_infoState_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 8, v_snapshotTasks_1726_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_st_ref_set(v___y_1714_, v___x_1735_);
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
}
v___jp_1741_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1765_; 
v___x_1750_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1697_);
v___x_1751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_1750_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_inc_ref_n(v___y_1745_, 2);
v___x_1756_ = l_Lean_FileMap_toPosition(v___y_1745_, v___y_1748_);
lean_dec(v___y_1748_);
v___x_1757_ = l_Lean_FileMap_toPosition(v___y_1745_, v___y_1749_);
lean_dec(v___y_1749_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
v___x_1759_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1747_ == 0)
{
lean_del_object(v___x_1754_);
lean_dec_ref(v___y_1742_);
v___y_1706_ = v___y_1744_;
v___y_1707_ = v___y_1743_;
v___y_1708_ = v_a_1752_;
v___y_1709_ = v___x_1759_;
v___y_1710_ = v___x_1756_;
v___y_1711_ = v___y_1746_;
v___y_1712_ = v___x_1758_;
v___y_1713_ = v___y_1702_;
v___y_1714_ = v___y_1703_;
goto v___jp_1705_;
}
else
{
uint8_t v___x_1760_; 
lean_inc(v_a_1752_);
v___x_1760_ = l_Lean_MessageData_hasTag(v___y_1742_, v_a_1752_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_dec_ref(v___x_1758_);
lean_dec_ref(v___x_1756_);
lean_dec(v_a_1752_);
v___x_1761_ = lean_box(0);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1761_);
v___x_1763_ = v___x_1754_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
lean_del_object(v___x_1754_);
v___y_1706_ = v___y_1744_;
v___y_1707_ = v___y_1743_;
v___y_1708_ = v_a_1752_;
v___y_1709_ = v___x_1759_;
v___y_1710_ = v___x_1756_;
v___y_1711_ = v___y_1746_;
v___y_1712_ = v___x_1758_;
v___y_1713_ = v___y_1702_;
v___y_1714_ = v___y_1703_;
goto v___jp_1705_;
}
}
}
}
v___jp_1766_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Syntax_getTailPos_x3f(v___y_1773_, v___y_1769_);
lean_dec(v___y_1773_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_inc(v___y_1774_);
v___y_1742_ = v___y_1767_;
v___y_1743_ = v___y_1769_;
v___y_1744_ = v___y_1768_;
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___y_1774_;
goto v___jp_1741_;
}
else
{
lean_object* v_val_1776_; 
v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_val_1776_);
lean_dec_ref(v___x_1775_);
v___y_1742_ = v___y_1767_;
v___y_1743_ = v___y_1769_;
v___y_1744_ = v___y_1768_;
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1774_;
v___y_1749_ = v_val_1776_;
goto v___jp_1741_;
}
}
v___jp_1777_:
{
lean_object* v_ref_1785_; lean_object* v___x_1786_; 
v_ref_1785_ = l_Lean_replaceRef(v_ref_1696_, v___y_1781_);
v___x_1786_ = l_Lean_Syntax_getPos_x3f(v_ref_1785_, v___y_1779_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
v___y_1767_ = v___y_1778_;
v___y_1768_ = v___y_1784_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1782_;
v___y_1772_ = v___y_1783_;
v___y_1773_ = v_ref_1785_;
v___y_1774_ = v___x_1787_;
goto v___jp_1766_;
}
else
{
lean_object* v_val_1788_; 
v_val_1788_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_val_1788_);
lean_dec_ref(v___x_1786_);
v___y_1767_ = v___y_1778_;
v___y_1768_ = v___y_1784_;
v___y_1769_ = v___y_1779_;
v___y_1770_ = v___y_1780_;
v___y_1771_ = v___y_1782_;
v___y_1772_ = v___y_1783_;
v___y_1773_ = v_ref_1785_;
v___y_1774_ = v_val_1788_;
goto v___jp_1766_;
}
}
v___jp_1790_:
{
if (v___y_1797_ == 0)
{
v___y_1778_ = v___y_1791_;
v___y_1779_ = v___y_1796_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1795_;
v___y_1784_ = v_severity_1698_;
goto v___jp_1777_;
}
else
{
v___y_1778_ = v___y_1791_;
v___y_1779_ = v___y_1796_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1795_;
v___y_1784_ = v___x_1789_;
goto v___jp_1777_;
}
}
v___jp_1798_:
{
if (v___y_1799_ == 0)
{
lean_object* v_fileName_1800_; lean_object* v_fileMap_1801_; lean_object* v_options_1802_; lean_object* v_ref_1803_; uint8_t v_suppressElabErrors_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; uint8_t v___x_1808_; uint8_t v___x_1809_; 
v_fileName_1800_ = lean_ctor_get(v___y_1702_, 0);
v_fileMap_1801_ = lean_ctor_get(v___y_1702_, 1);
v_options_1802_ = lean_ctor_get(v___y_1702_, 2);
v_ref_1803_ = lean_ctor_get(v___y_1702_, 5);
v_suppressElabErrors_1804_ = lean_ctor_get_uint8(v___y_1702_, sizeof(void*)*14 + 1);
v___x_1805_ = lean_box(v___y_1799_);
v___x_1806_ = lean_box(v_suppressElabErrors_1804_);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1807_, 0, v___x_1805_);
lean_closure_set(v___f_1807_, 1, v___x_1806_);
v___x_1808_ = 1;
v___x_1809_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1698_, v___x_1808_);
if (v___x_1809_ == 0)
{
v___y_1791_ = v___f_1807_;
v___y_1792_ = v_fileMap_1801_;
v___y_1793_ = v_ref_1803_;
v___y_1794_ = v_fileName_1800_;
v___y_1795_ = v_suppressElabErrors_1804_;
v___y_1796_ = v___y_1799_;
v___y_1797_ = v___x_1809_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = l_Lean_warningAsError;
v___x_1811_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1802_, v___x_1810_);
v___y_1791_ = v___f_1807_;
v___y_1792_ = v_fileMap_1801_;
v___y_1793_ = v_ref_1803_;
v___y_1794_ = v_fileName_1800_;
v___y_1795_ = v_suppressElabErrors_1804_;
v___y_1796_ = v___y_1799_;
v___y_1797_ = v___x_1811_;
goto v___jp_1790_;
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v_msgData_1697_);
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object* v_ref_1816_, lean_object* v_msgData_1817_, lean_object* v_severity_1818_, lean_object* v_isSilent_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
uint8_t v_severity_boxed_1825_; uint8_t v_isSilent_boxed_1826_; lean_object* v_res_1827_; 
v_severity_boxed_1825_ = lean_unbox(v_severity_1818_);
v_isSilent_boxed_1826_ = lean_unbox(v_isSilent_1819_);
v_res_1827_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1816_, v_msgData_1817_, v_severity_boxed_1825_, v_isSilent_boxed_1826_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_ref_1816_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object* v_as_1828_, size_t v_sz_1829_, size_t v_i_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1830_, v_sz_1829_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1831_);
return v___x_1840_;
}
else
{
lean_object* v_ref_1841_; lean_object* v_a_1842_; uint8_t v_severity_1843_; lean_object* v_data_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; 
v_ref_1841_ = lean_ctor_get(v___y_1836_, 5);
v_a_1842_ = lean_array_uget_borrowed(v_as_1828_, v_i_1830_);
v_severity_1843_ = lean_ctor_get_uint8(v_a_1842_, sizeof(void*)*5 + 1);
v_data_1844_ = lean_ctor_get(v_a_1842_, 4);
v___x_1845_ = 0;
lean_inc(v_data_1844_);
v___x_1846_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1841_, v_data_1844_, v_severity_1843_, v___x_1845_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; 
lean_dec_ref(v___x_1846_);
v___x_1847_ = lean_box(0);
v___x_1848_ = ((size_t)1ULL);
v___x_1849_ = lean_usize_add(v_i_1830_, v___x_1848_);
v_i_1830_ = v___x_1849_;
v_b_1831_ = v___x_1847_;
goto _start;
}
else
{
return v___x_1846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object* v_as_1851_, lean_object* v_sz_1852_, lean_object* v_i_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
size_t v_sz_boxed_1862_; size_t v_i_boxed_1863_; lean_object* v_res_1864_; 
v_sz_boxed_1862_ = lean_unbox_usize(v_sz_1852_);
lean_dec(v_sz_1852_);
v_i_boxed_1863_ = lean_unbox_usize(v_i_1853_);
lean_dec(v_i_1853_);
v_res_1864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_1851_, v_sz_boxed_1862_, v_i_boxed_1863_, v_b_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec_ref(v_as_1851_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t v_flag_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v_infoState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_traceState_1874_; lean_object* v_cache_1875_; lean_object* v_messages_1876_; lean_object* v_snapshotTasks_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1897_; 
v___x_1868_ = lean_st_ref_take(v___y_1866_);
v_infoState_1869_ = lean_ctor_get(v___x_1868_, 7);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_traceState_1874_ = lean_ctor_get(v___x_1868_, 4);
v_cache_1875_ = lean_ctor_get(v___x_1868_, 5);
v_messages_1876_ = lean_ctor_get(v___x_1868_, 6);
v_snapshotTasks_1877_ = lean_ctor_get(v___x_1868_, 8);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1879_ = v___x_1868_;
v_isShared_1880_ = v_isSharedCheck_1897_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snapshotTasks_1877_);
lean_inc(v_infoState_1869_);
lean_inc(v_messages_1876_);
lean_inc(v_cache_1875_);
lean_inc(v_traceState_1874_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1897_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_assignment_1881_; lean_object* v_lazyAssignment_1882_; lean_object* v_trees_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1896_; 
v_assignment_1881_ = lean_ctor_get(v_infoState_1869_, 0);
v_lazyAssignment_1882_ = lean_ctor_get(v_infoState_1869_, 1);
v_trees_1883_ = lean_ctor_get(v_infoState_1869_, 2);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_infoState_1869_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1885_ = v_infoState_1869_;
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_trees_1883_);
lean_inc(v_lazyAssignment_1882_);
lean_inc(v_assignment_1881_);
lean_dec(v_infoState_1869_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1896_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_assignment_1881_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_lazyAssignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_trees_1883_);
v___x_1888_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3, v_flag_1865_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 7, v___x_1888_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_traceState_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v_cache_1875_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_messages_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_snapshotTasks_1877_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_st_ref_set(v___y_1866_, v___x_1890_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object* v_flag_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_flag_boxed_1901_; lean_object* v_res_1902_; 
v_flag_boxed_1901_ = lean_unbox(v_flag_1898_);
v_res_1902_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_1901_, v___y_1899_);
lean_dec(v___y_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t v_flag_1903_, lean_object* v_x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v_infoState_1913_; uint8_t v_enabled_1914_; lean_object* v_a_1916_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1912_ = lean_st_ref_get(v___y_1910_);
v_infoState_1913_ = lean_ctor_get(v___x_1912_, 7);
lean_inc_ref(v_infoState_1913_);
lean_dec(v___x_1912_);
v_enabled_1914_ = lean_ctor_get_uint8(v_infoState_1913_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1913_);
v___x_1926_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_1903_, v___y_1910_);
lean_dec_ref(v___x_1926_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
v___x_1927_ = lean_apply_7(v_x_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, lean_box(0));
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1914_, v___y_1910_);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1929_, 0);
lean_dec(v_unused_1937_);
v___x_1931_ = v___x_1929_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v___x_1929_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_a_1928_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1928_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1938_; 
v_a_1938_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1927_);
v_a_1916_ = v_a_1938_;
goto v___jp_1915_;
}
v___jp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v___x_1917_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1914_, v___y_1910_);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1917_, 0);
lean_dec(v_unused_1925_);
v___x_1919_ = v___x_1917_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_dec(v___x_1917_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 1);
lean_ctor_set(v___x_1919_, 0, v_a_1916_);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1916_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object* v_flag_1939_, lean_object* v_x_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
uint8_t v_flag_boxed_1948_; lean_object* v_res_1949_; 
v_flag_boxed_1948_ = lean_unbox(v_flag_1939_);
v_res_1949_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_boxed_1948_, v_x_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object* v_msgData_1950_, uint8_t v_severity_1951_, uint8_t v_isSilent_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_ref_1960_; lean_object* v___x_1961_; 
v_ref_1960_ = lean_ctor_get(v___y_1957_, 5);
v___x_1961_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1960_, v_msgData_1950_, v_severity_1951_, v_isSilent_1952_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object* v_msgData_1962_, lean_object* v_severity_1963_, lean_object* v_isSilent_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
uint8_t v_severity_boxed_1972_; uint8_t v_isSilent_boxed_1973_; lean_object* v_res_1974_; 
v_severity_boxed_1972_ = lean_unbox(v_severity_1963_);
v_isSilent_boxed_1973_ = lean_unbox(v_isSilent_1964_);
v_res_1974_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1962_, v_severity_boxed_1972_, v_isSilent_boxed_1973_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object* v_msgData_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
uint8_t v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = 2;
v___x_1984_ = 0;
v___x_1985_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1975_, v___x_1983_, v___x_1984_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object* v_msgData_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v_msgData_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object* v_as_1995_, size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_b_1998_);
return v___x_2007_;
}
else
{
lean_object* v_a_2008_; lean_object* v_snd_2009_; lean_object* v_snd_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2008_ = lean_array_uget_borrowed(v_as_1995_, v_i_1997_);
v_snd_2009_ = lean_ctor_get(v_a_2008_, 1);
v_snd_2010_ = lean_ctor_get(v_snd_2009_, 1);
lean_inc(v_snd_2010_);
v___x_2011_ = l_Lean_Parser_Error_toString(v_snd_2010_);
v___x_2012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
v___x_2013_ = l_Lean_MessageData_ofFormat(v___x_2012_);
v___x_2014_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2013_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; size_t v___x_2016_; size_t v___x_2017_; 
lean_dec_ref(v___x_2014_);
v___x_2015_ = lean_box(0);
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_1997_, v___x_2016_);
v_i_1997_ = v___x_2017_;
v_b_1998_ = v___x_2015_;
goto _start;
}
else
{
return v___x_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object* v_as_2019_, lean_object* v_sz_2020_, lean_object* v_i_2021_, lean_object* v_b_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
size_t v_sz_boxed_2030_; size_t v_i_boxed_2031_; lean_object* v_res_2032_; 
v_sz_boxed_2030_ = lean_unbox_usize(v_sz_2020_);
lean_dec(v_sz_2020_);
v_i_boxed_2031_ = lean_unbox_usize(v_i_2021_);
lean_dec(v_i_2021_);
v_res_2032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_2019_, v_sz_boxed_2030_, v_i_boxed_2031_, v_b_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec_ref(v_as_2019_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2052_, lean_object* v_docComment_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v_env_2062_; lean_object* v_fileName_2063_; lean_object* v_options_2064_; lean_object* v_currNamespace_2065_; lean_object* v_openDecls_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2061_ = lean_st_ref_get(v_a_2059_);
v_env_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref_n(v_env_2062_, 2);
lean_dec(v___x_2061_);
v_fileName_2063_ = lean_ctor_get(v_a_2058_, 0);
v_options_2064_ = lean_ctor_get(v_a_2058_, 2);
v_currNamespace_2065_ = lean_ctor_get(v_a_2058_, 6);
v_openDecls_2066_ = lean_ctor_get(v_a_2058_, 7);
v___x_2067_ = lean_string_utf8_byte_size(v_docComment_2053_);
lean_inc_ref_n(v_docComment_2053_, 2);
v___x_2068_ = l_Lean_FileMap_ofString(v_docComment_2053_);
lean_inc_ref(v___x_2068_);
lean_inc_ref(v_fileName_2063_);
v___x_2069_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2069_, 0, v_docComment_2053_);
lean_ctor_set(v___x_2069_, 1, v_fileName_2063_);
lean_ctor_set(v___x_2069_, 2, v___x_2068_);
lean_ctor_set(v___x_2069_, 3, v___x_2067_);
lean_inc(v_openDecls_2066_);
lean_inc(v_currNamespace_2065_);
lean_inc_ref(v_options_2064_);
v___x_2070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2070_, 0, v_env_2062_);
lean_ctor_set(v___x_2070_, 1, v_options_2064_);
lean_ctor_set(v___x_2070_, 2, v_currNamespace_2065_);
lean_ctor_set(v___x_2070_, 3, v_openDecls_2066_);
v___x_2071_ = l_Lean_Parser_mkParserState(v_docComment_2053_);
lean_dec_ref(v_docComment_2053_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__2));
v___x_2074_ = l_Lean_Parser_getTokenTable(v_env_2062_);
v___x_2075_ = l_Lean_Parser_ParserFn_run(v___x_2073_, v___x_2069_, v___x_2070_, v___x_2074_, v___x_2071_);
lean_inc_ref(v___x_2075_);
v___x_2076_ = l_Lean_Parser_ParserState_allErrors(v___x_2075_);
v___x_2077_ = lean_array_get_size(v___x_2076_);
v___x_2078_ = lean_nat_dec_eq(v___x_2077_, v___x_2072_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v___x_2068_);
lean_dec(v_declName_2052_);
v___x_2079_ = lean_box(0);
v_sz_2080_ = lean_array_size(v___x_2076_);
v___x_2081_ = ((size_t)0ULL);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_2076_, v_sz_2080_, v___x_2081_, v___x_2079_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec_ref(v___x_2076_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v___x_2082_, 0);
lean_dec(v_unused_2091_);
v___x_2084_ = v___x_2082_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_dec(v___x_2082_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_a_2092_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2082_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2082_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v___x_2100_; 
lean_dec_ref(v___x_2076_);
v___x_2100_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2059_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v_a_2103_; lean_object* v_stxStack_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; size_t v_sz_2126_; size_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
v_stxStack_2121_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_ref(v_stxStack_2121_);
lean_dec_ref(v___x_2075_);
v___x_2122_ = 0;
v___x_2123_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2121_);
lean_dec_ref(v_stxStack_2121_);
v___x_2124_ = l_Lean_Syntax_getArgs(v___x_2123_);
lean_dec(v___x_2123_);
v___x_2125_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__6));
v_sz_2126_ = lean_array_size(v___x_2124_);
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_2126_, v___x_2127_, v___x_2124_);
v___x_2129_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2129_, 0, v___x_2128_);
v___x_2130_ = 1;
v___x_2131_ = lean_box(v___x_2130_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_versoDocStringFromString___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2132_, 0, v___x_2068_);
lean_closure_set(v___f_2132_, 1, v_declName_2052_);
lean_closure_set(v___f_2132_, 2, v___x_2125_);
lean_closure_set(v___f_2132_, 3, v___x_2129_);
lean_closure_set(v___f_2132_, 4, v___x_2131_);
v___x_2133_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_2122_, v___f_2132_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2059_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref(v___x_2135_);
v___x_2137_ = l_Lean_Core_setMessageLog___redArg(v_a_2101_, v_a_2059_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; size_t v_sz_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v___x_2137_);
v___x_2138_ = l_Lean_MessageLog_toArray(v_a_2136_);
lean_dec(v_a_2136_);
v___x_2139_ = lean_box(0);
v_sz_2140_ = lean_array_size(v___x_2138_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_2138_, v_sz_2140_, v___x_2127_, v___x_2139_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec_ref(v___x_2138_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v___x_2141_, 0);
lean_dec(v_unused_2149_);
v___x_2143_ = v___x_2141_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v___x_2141_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v_a_2134_);
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2134_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec(v_a_2134_);
v_a_2150_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2141_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2141_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_a_2136_);
lean_dec(v_a_2134_);
v_a_2158_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2137_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2137_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; 
lean_dec(v_a_2134_);
v_a_2166_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2135_);
v_a_2103_ = v_a_2166_;
goto v___jp_2102_;
}
}
else
{
lean_object* v_a_2167_; 
v_a_2167_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2133_);
v_a_2103_ = v_a_2167_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Core_setMessageLog___redArg(v_a_2101_, v_a_2059_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2104_, 0);
lean_dec(v_unused_2112_);
v___x_2106_ = v___x_2104_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_dec(v___x_2104_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
lean_ctor_set(v___x_2106_, 0, v_a_2103_);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2103_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_a_2103_);
v_a_2113_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2104_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2104_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v___x_2068_);
lean_dec(v_declName_2052_);
v_a_2168_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2100_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2100_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2176_, lean_object* v_docComment_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_versoDocStringFromString(v_declName_2176_, v_docComment_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
lean_dec(v_a_2179_);
lean_dec_ref(v_a_2178_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t v_flag_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_2186_, v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object* v_flag_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v_flag_boxed_2203_; lean_object* v_res_2204_; 
v_flag_boxed_2203_ = lean_unbox(v_flag_2195_);
v_res_2204_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_2203_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object* v_00_u03b1_2205_, uint8_t v_flag_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_2206_, v_x_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object* v_00_u03b1_2216_, lean_object* v_flag_2217_, lean_object* v_x_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
uint8_t v_flag_boxed_2226_; lean_object* v_res_2227_; 
v_flag_boxed_2226_ = lean_unbox(v_flag_2217_);
v_res_2227_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(v_00_u03b1_2216_, v_flag_boxed_2226_, v_x_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object* v_ref_2228_, lean_object* v_msgData_2229_, uint8_t v_severity_2230_, uint8_t v_isSilent_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2228_, v_msgData_2229_, v_severity_2230_, v_isSilent_2231_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object* v_ref_2240_, lean_object* v_msgData_2241_, lean_object* v_severity_2242_, lean_object* v_isSilent_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
uint8_t v_severity_boxed_2251_; uint8_t v_isSilent_boxed_2252_; lean_object* v_res_2253_; 
v_severity_boxed_2251_ = lean_unbox(v_severity_2242_);
v_isSilent_boxed_2252_ = lean_unbox(v_isSilent_2243_);
v_res_2253_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(v_ref_2240_, v_msgData_2241_, v_severity_boxed_2251_, v_isSilent_boxed_2252_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v_ref_2240_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2254_, lean_object* v_declName_2255_, lean_object* v_env_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = l_Lean_docStringExt;
v___x_2258_ = l_String_removeLeadingSpaces(v_docString_2254_);
v___x_2259_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2257_, v_env_2256_, v_declName_2255_, v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2260_, lean_object* v_modifyEnv_2261_, lean_object* v_docString_2262_){
_start:
{
lean_object* v___f_2263_; lean_object* v___x_2264_; 
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2263_, 0, v_docString_2262_);
lean_closure_set(v___f_2263_, 1, v_declName_2260_);
v___x_2264_ = lean_apply_1(v_modifyEnv_2261_, v___f_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_docComment_2267_, lean_object* v_toBind_2268_, lean_object* v___f_2269_, lean_object* v_____r_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = l_Lean_getDocStringText___redArg(v_inst_2265_, v_inst_2266_, v_docComment_2267_);
v___x_2272_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2271_, v___f_2269_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_docComment_2278_, lean_object* v_toBind_2279_, lean_object* v___f_2280_, lean_object* v_____r_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = l_Lean_validateDocComment___redArg(v_inst_2273_, v_inst_2274_, v_inst_2275_, v_inst_2276_, v_inst_2277_, v_docComment_2278_);
v___x_2283_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v___x_2282_, v___f_2280_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_docComment_2289_, lean_object* v_toBind_2290_, lean_object* v___f_2291_, lean_object* v_____r_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2284_, v_inst_2285_, v_inst_2286_, v_inst_2287_, v_inst_2288_, v_docComment_2289_, v_toBind_2290_, v___f_2291_, v_____r_2292_);
lean_dec(v_docComment_2289_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2294_, lean_object* v_____r_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_apply_1(v___f_2294_, v_____r_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2303_, lean_object* v_declName_2304_, uint8_t v___x_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_toBind_2308_, lean_object* v___f_2309_, lean_object* v_____do__lift_2310_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2310_, v_declName_2304_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_dec(v___f_2309_);
lean_dec(v_toBind_2308_);
lean_dec_ref(v_inst_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec(v_declName_2304_);
goto v___jp_2311_;
}
else
{
lean_dec_ref(v___x_2314_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v___f_2303_);
v___x_2315_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2316_ = l_Lean_MessageData_ofConstName(v_declName_2304_, v___x_2305_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_throwError___redArg(v_inst_2306_, v_inst_2307_, v___x_2319_);
v___x_2321_ = lean_apply_4(v_toBind_2308_, lean_box(0), lean_box(0), v___x_2320_, v___f_2309_);
return v___x_2321_;
}
else
{
lean_dec(v___f_2309_);
lean_dec(v_toBind_2308_);
lean_dec_ref(v_inst_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec(v_declName_2304_);
goto v___jp_2311_;
}
}
v___jp_2311_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_apply_1(v___f_2303_, v___x_2312_);
return v___x_2313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2322_, lean_object* v_declName_2323_, lean_object* v___x_2324_, lean_object* v_inst_2325_, lean_object* v_inst_2326_, lean_object* v_toBind_2327_, lean_object* v___f_2328_, lean_object* v_____do__lift_2329_){
_start:
{
uint8_t v___x_390__boxed_2330_; lean_object* v_res_2331_; 
v___x_390__boxed_2330_ = lean_unbox(v___x_2324_);
v_res_2331_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2322_, v_declName_2323_, v___x_390__boxed_2330_, v_inst_2325_, v_inst_2326_, v_toBind_2327_, v___f_2328_, v_____do__lift_2329_);
lean_dec_ref(v_____do__lift_2329_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_declName_2339_, lean_object* v_docComment_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_Name_isAnonymous(v_declName_2339_);
if (v___x_2341_ == 0)
{
lean_object* v_toBind_2342_; lean_object* v_getEnv_2343_; lean_object* v_modifyEnv_2344_; lean_object* v___f_2345_; lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; 
v_toBind_2342_ = lean_ctor_get(v_inst_2332_, 1);
lean_inc_n(v_toBind_2342_, 4);
v_getEnv_2343_ = lean_ctor_get(v_inst_2335_, 0);
lean_inc(v_getEnv_2343_);
v_modifyEnv_2344_ = lean_ctor_get(v_inst_2335_, 1);
lean_inc(v_modifyEnv_2344_);
lean_dec_ref(v_inst_2335_);
lean_inc(v_declName_2339_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2345_, 0, v_declName_2339_);
lean_closure_set(v___f_2345_, 1, v_modifyEnv_2344_);
lean_inc(v_docComment_2340_);
lean_inc_ref(v_inst_2336_);
lean_inc_ref_n(v_inst_2332_, 2);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2346_, 0, v_inst_2332_);
lean_closure_set(v___f_2346_, 1, v_inst_2336_);
lean_closure_set(v___f_2346_, 2, v_docComment_2340_);
lean_closure_set(v___f_2346_, 3, v_toBind_2342_);
lean_closure_set(v___f_2346_, 4, v___f_2345_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2347_, 0, v_inst_2332_);
lean_closure_set(v___f_2347_, 1, v_inst_2333_);
lean_closure_set(v___f_2347_, 2, v_inst_2337_);
lean_closure_set(v___f_2347_, 3, v_inst_2338_);
lean_closure_set(v___f_2347_, 4, v_inst_2334_);
lean_closure_set(v___f_2347_, 5, v_docComment_2340_);
lean_closure_set(v___f_2347_, 6, v_toBind_2342_);
lean_closure_set(v___f_2347_, 7, v___f_2346_);
lean_inc_ref(v___f_2347_);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2348_, 0, v___f_2347_);
v___x_2349_ = lean_box(v___x_2341_);
v___f_2350_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2350_, 0, v___f_2347_);
lean_closure_set(v___f_2350_, 1, v_declName_2339_);
lean_closure_set(v___f_2350_, 2, v___x_2349_);
lean_closure_set(v___f_2350_, 3, v_inst_2332_);
lean_closure_set(v___f_2350_, 4, v_inst_2336_);
lean_closure_set(v___f_2350_, 5, v_toBind_2342_);
lean_closure_set(v___f_2350_, 6, v___f_2348_);
v___x_2351_ = lean_apply_4(v_toBind_2342_, lean_box(0), lean_box(0), v_getEnv_2343_, v___f_2350_);
return v___x_2351_;
}
else
{
lean_object* v_toApplicative_2352_; lean_object* v_toPure_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec(v_docComment_2340_);
lean_dec(v_declName_2339_);
lean_dec(v_inst_2338_);
lean_dec_ref(v_inst_2337_);
lean_dec_ref(v_inst_2336_);
lean_dec_ref(v_inst_2335_);
lean_dec(v_inst_2334_);
lean_dec(v_inst_2333_);
v_toApplicative_2352_ = lean_ctor_get(v_inst_2332_, 0);
lean_inc_ref(v_toApplicative_2352_);
lean_dec_ref(v_inst_2332_);
v_toPure_2353_ = lean_ctor_get(v_toApplicative_2352_, 1);
lean_inc(v_toPure_2353_);
lean_dec_ref(v_toApplicative_2352_);
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_apply_2(v_toPure_2353_, lean_box(0), v___x_2354_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_declName_2364_, lean_object* v_docComment_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_addMarkdownDocString___redArg(v_inst_2357_, v_inst_2358_, v_inst_2359_, v_inst_2360_, v_inst_2361_, v_inst_2362_, v_inst_2363_, v_declName_2364_, v_docComment_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2367_, lean_object* v_docs_2368_, lean_object* v_env_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_versoDocStringExt;
v___x_2371_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2370_, v_env_2369_, v_declName_2367_, v_docs_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_2372_, lean_object* v___f_2373_, lean_object* v_____r_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_apply_1(v_modifyEnv_2372_, v___f_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_2378_, lean_object* v_modifyEnv_2379_, lean_object* v___f_2380_, uint8_t v___x_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_toBind_2384_, lean_object* v___f_2385_, lean_object* v_____do__lift_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2386_, v_declName_2378_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
lean_dec(v___f_2385_);
lean_dec(v_toBind_2384_);
lean_dec_ref(v_inst_2383_);
lean_dec_ref(v_inst_2382_);
lean_dec(v_declName_2378_);
v___x_2388_ = lean_apply_1(v_modifyEnv_2379_, v___f_2380_);
return v___x_2388_;
}
else
{
lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2405_; 
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2387_, 0);
lean_dec(v_unused_2406_);
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2405_;
goto v_resetjp_2389_;
}
else
{
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2405_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
if (v___x_2381_ == 0)
{
lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
lean_dec_ref(v___f_2380_);
lean_dec(v_modifyEnv_2379_);
v___x_2392_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2393_ = 1;
v___x_2394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2378_, v___x_2393_);
v___x_2395_ = lean_string_append(v___x_2392_, v___x_2394_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2397_ = lean_string_append(v___x_2395_, v___x_2396_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set_tag(v___x_2390_, 3);
lean_ctor_set(v___x_2390_, 0, v___x_2397_);
v___x_2399_ = v___x_2390_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = l_Lean_MessageData_ofFormat(v___x_2399_);
v___x_2401_ = l_Lean_throwError___redArg(v_inst_2382_, v_inst_2383_, v___x_2400_);
v___x_2402_ = lean_apply_4(v_toBind_2384_, lean_box(0), lean_box(0), v___x_2401_, v___f_2385_);
return v___x_2402_;
}
}
else
{
lean_object* v___x_2404_; 
lean_del_object(v___x_2390_);
lean_dec(v___f_2385_);
lean_dec(v_toBind_2384_);
lean_dec_ref(v_inst_2383_);
lean_dec_ref(v_inst_2382_);
lean_dec(v_declName_2378_);
v___x_2404_ = lean_apply_1(v_modifyEnv_2379_, v___f_2380_);
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_2407_, lean_object* v_modifyEnv_2408_, lean_object* v___f_2409_, lean_object* v___x_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_toBind_2413_, lean_object* v___f_2414_, lean_object* v_____do__lift_2415_){
_start:
{
uint8_t v___x_304__boxed_2416_; lean_object* v_res_2417_; 
v___x_304__boxed_2416_ = lean_unbox(v___x_2410_);
v_res_2417_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_2407_, v_modifyEnv_2408_, v___f_2409_, v___x_304__boxed_2416_, v_inst_2411_, v_inst_2412_, v_toBind_2413_, v___f_2414_, v_____do__lift_2415_);
lean_dec_ref(v_____do__lift_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_declName_2421_, lean_object* v_docs_2422_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = l_Lean_Name_isAnonymous(v_declName_2421_);
if (v___x_2423_ == 0)
{
lean_object* v_toBind_2424_; lean_object* v_getEnv_2425_; lean_object* v_modifyEnv_2426_; lean_object* v___f_2427_; lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___f_2430_; lean_object* v___x_2431_; 
v_toBind_2424_ = lean_ctor_get(v_inst_2418_, 1);
lean_inc_n(v_toBind_2424_, 2);
v_getEnv_2425_ = lean_ctor_get(v_inst_2419_, 0);
lean_inc(v_getEnv_2425_);
v_modifyEnv_2426_ = lean_ctor_get(v_inst_2419_, 1);
lean_inc_n(v_modifyEnv_2426_, 2);
lean_dec_ref(v_inst_2419_);
lean_inc(v_declName_2421_);
v___f_2427_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2427_, 0, v_declName_2421_);
lean_closure_set(v___f_2427_, 1, v_docs_2422_);
lean_inc_ref(v___f_2427_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2428_, 0, v_modifyEnv_2426_);
lean_closure_set(v___f_2428_, 1, v___f_2427_);
v___x_2429_ = lean_box(v___x_2423_);
v___f_2430_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2430_, 0, v_declName_2421_);
lean_closure_set(v___f_2430_, 1, v_modifyEnv_2426_);
lean_closure_set(v___f_2430_, 2, v___f_2427_);
lean_closure_set(v___f_2430_, 3, v___x_2429_);
lean_closure_set(v___f_2430_, 4, v_inst_2418_);
lean_closure_set(v___f_2430_, 5, v_inst_2420_);
lean_closure_set(v___f_2430_, 6, v_toBind_2424_);
lean_closure_set(v___f_2430_, 7, v___f_2428_);
v___x_2431_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v_getEnv_2425_, v___f_2430_);
return v___x_2431_;
}
else
{
lean_object* v_toApplicative_2432_; lean_object* v_toPure_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
lean_dec_ref(v_docs_2422_);
lean_dec(v_declName_2421_);
lean_dec_ref(v_inst_2420_);
lean_dec_ref(v_inst_2419_);
v_toApplicative_2432_ = lean_ctor_get(v_inst_2418_, 0);
lean_inc_ref(v_toApplicative_2432_);
lean_dec_ref(v_inst_2418_);
v_toPure_2433_ = lean_ctor_get(v_toApplicative_2432_, 1);
lean_inc(v_toPure_2433_);
lean_dec_ref(v_toApplicative_2432_);
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_apply_2(v_toPure_2433_, lean_box(0), v___x_2434_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_declName_2441_, lean_object* v_docs_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2437_, v_inst_2438_, v_inst_2440_, v_declName_2441_, v_docs_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_declName_2449_, lean_object* v_docs_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_addVersoDocStringCore(v_m_2444_, v_inst_2445_, v_inst_2446_, v_inst_2447_, v_inst_2448_, v_declName_2449_, v_docs_2450_);
lean_dec(v_inst_2447_);
return v_res_2451_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_____do__lift_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2459_, v_docs_2455_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec_ref(v_inst_2458_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_2463_ = l_Lean_stringToMessageData(v_a_2461_);
v___x_2464_ = l_Lean_indentD(v___x_2463_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2462_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = l_Lean_throwError___redArg(v_inst_2456_, v_inst_2457_, v___x_2465_);
return v___x_2466_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
lean_dec_ref(v_inst_2457_);
lean_dec_ref(v_inst_2456_);
v_a_2467_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2467_);
lean_dec_ref(v___x_2460_);
v___x_2468_ = l_Lean_setEnv___redArg(v_inst_2458_, v_a_2467_);
return v___x_2468_;
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_toBind_2474_, lean_object* v_getEnv_2475_, lean_object* v___f_2476_, lean_object* v_____do__lift_2477_){
_start:
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = l_Lean_getMainModuleDoc(v_____do__lift_2477_);
v___x_2479_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2478_);
lean_dec_ref(v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec(v___f_2476_);
lean_dec(v_getEnv_2475_);
lean_dec(v_toBind_2474_);
v___x_2480_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2481_ = l_Lean_throwError___redArg(v_inst_2472_, v_inst_2473_, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; 
lean_dec_ref(v_inst_2473_);
lean_dec_ref(v_inst_2472_);
v___x_2482_ = lean_apply_4(v_toBind_2474_, lean_box(0), lean_box(0), v_getEnv_2475_, v___f_2476_);
return v___x_2482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_docs_2486_){
_start:
{
lean_object* v_toBind_2487_; lean_object* v_getEnv_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
v_toBind_2487_ = lean_ctor_get(v_inst_2483_, 1);
lean_inc_n(v_toBind_2487_, 2);
v_getEnv_2488_ = lean_ctor_get(v_inst_2484_, 0);
lean_inc_n(v_getEnv_2488_, 2);
lean_inc_ref(v_inst_2485_);
lean_inc_ref(v_inst_2483_);
v___f_2489_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2489_, 0, v_docs_2486_);
lean_closure_set(v___f_2489_, 1, v_inst_2483_);
lean_closure_set(v___f_2489_, 2, v_inst_2485_);
lean_closure_set(v___f_2489_, 3, v_inst_2484_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2490_, 0, v_inst_2483_);
lean_closure_set(v___f_2490_, 1, v_inst_2485_);
lean_closure_set(v___f_2490_, 2, v_toBind_2487_);
lean_closure_set(v___f_2490_, 3, v_getEnv_2488_);
lean_closure_set(v___f_2490_, 4, v___f_2489_);
v___x_2491_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v_getEnv_2488_, v___f_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_docs_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2493_, v_inst_2494_, v_inst_2496_, v_docs_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_docs_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_addVersoModDocStringCore(v_m_2499_, v_inst_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_docs_2504_);
lean_dec(v_inst_2502_);
return v_res_2505_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2512_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
lean_ctor_set(v___x_2512_, 2, v___x_2511_);
lean_ctor_set(v___x_2512_, 3, v___x_2511_);
lean_ctor_set(v___x_2512_, 4, v___x_2511_);
lean_ctor_set(v___x_2512_, 5, v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2513_, lean_object* v_docs_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___y_2523_; lean_object* v___y_2524_; uint8_t v___x_2563_; 
v___x_2563_ = l_Lean_Name_isAnonymous(v_declName_2513_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v_env_2565_; lean_object* v___x_2566_; 
v___x_2564_ = lean_st_ref_get(v___y_2520_);
v_env_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc_ref(v_env_2565_);
lean_dec(v___x_2564_);
v___x_2566_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2565_, v_declName_2513_);
lean_dec_ref(v_env_2565_);
if (lean_obj_tag(v___x_2566_) == 0)
{
v___y_2523_ = v___y_2518_;
v___y_2524_ = v___y_2520_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2581_; 
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2566_, 0);
lean_dec(v_unused_2582_);
v___x_2568_ = v___x_2566_;
v_isShared_2569_ = v_isSharedCheck_2581_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v___x_2566_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2581_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
if (v___x_2563_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_dec_ref(v_docs_2514_);
v___x_2570_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2571_ = 1;
v___x_2572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2513_, v___x_2571_);
v___x_2573_ = lean_string_append(v___x_2570_, v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2575_ = lean_string_append(v___x_2573_, v___x_2574_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 3);
lean_ctor_set(v___x_2568_, 0, v___x_2575_);
v___x_2577_ = v___x_2568_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
v___x_2579_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2578_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2579_;
}
}
else
{
lean_del_object(v___x_2568_);
v___y_2523_ = v___y_2518_;
v___y_2524_ = v___y_2520_;
goto v___jp_2522_;
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_dec_ref(v_docs_2514_);
lean_dec(v_declName_2513_);
v___x_2583_ = lean_box(0);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
v___jp_2522_:
{
lean_object* v___x_2525_; lean_object* v_env_2526_; lean_object* v_nextMacroScope_2527_; lean_object* v_ngen_2528_; lean_object* v_auxDeclNGen_2529_; lean_object* v_traceState_2530_; lean_object* v_messages_2531_; lean_object* v_infoState_2532_; lean_object* v_snapshotTasks_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2561_; 
v___x_2525_ = lean_st_ref_take(v___y_2524_);
v_env_2526_ = lean_ctor_get(v___x_2525_, 0);
v_nextMacroScope_2527_ = lean_ctor_get(v___x_2525_, 1);
v_ngen_2528_ = lean_ctor_get(v___x_2525_, 2);
v_auxDeclNGen_2529_ = lean_ctor_get(v___x_2525_, 3);
v_traceState_2530_ = lean_ctor_get(v___x_2525_, 4);
v_messages_2531_ = lean_ctor_get(v___x_2525_, 6);
v_infoState_2532_ = lean_ctor_get(v___x_2525_, 7);
v_snapshotTasks_2533_ = lean_ctor_get(v___x_2525_, 8);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2525_, 5);
lean_dec(v_unused_2562_);
v___x_2535_ = v___x_2525_;
v_isShared_2536_ = v_isSharedCheck_2561_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_snapshotTasks_2533_);
lean_inc(v_infoState_2532_);
lean_inc(v_messages_2531_);
lean_inc(v_traceState_2530_);
lean_inc(v_auxDeclNGen_2529_);
lean_inc(v_ngen_2528_);
lean_inc(v_nextMacroScope_2527_);
lean_inc(v_env_2526_);
lean_dec(v___x_2525_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2561_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2537_ = l_Lean_versoDocStringExt;
v___x_2538_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2537_, v_env_2526_, v_declName_2513_, v_docs_2514_);
v___x_2539_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 5, v___x_2539_);
lean_ctor_set(v___x_2535_, 0, v___x_2538_);
v___x_2541_ = v___x_2535_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_nextMacroScope_2527_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_ngen_2528_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_auxDeclNGen_2529_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v_traceState_2530_);
lean_ctor_set(v_reuseFailAlloc_2560_, 5, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2560_, 6, v_messages_2531_);
lean_ctor_set(v_reuseFailAlloc_2560_, 7, v_infoState_2532_);
lean_ctor_set(v_reuseFailAlloc_2560_, 8, v_snapshotTasks_2533_);
v___x_2541_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v_mctx_2544_; lean_object* v_zetaDeltaFVarIds_2545_; lean_object* v_postponed_2546_; lean_object* v_diag_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2558_; 
v___x_2542_ = lean_st_ref_set(v___y_2524_, v___x_2541_);
v___x_2543_ = lean_st_ref_take(v___y_2523_);
v_mctx_2544_ = lean_ctor_get(v___x_2543_, 0);
v_zetaDeltaFVarIds_2545_ = lean_ctor_get(v___x_2543_, 2);
v_postponed_2546_ = lean_ctor_get(v___x_2543_, 3);
v_diag_2547_ = lean_ctor_get(v___x_2543_, 4);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2558_ == 0)
{
lean_object* v_unused_2559_; 
v_unused_2559_ = lean_ctor_get(v___x_2543_, 1);
lean_dec(v_unused_2559_);
v___x_2549_ = v___x_2543_;
v_isShared_2550_ = v_isSharedCheck_2558_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_diag_2547_);
lean_inc(v_postponed_2546_);
lean_inc(v_zetaDeltaFVarIds_2545_);
lean_inc(v_mctx_2544_);
lean_dec(v___x_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2558_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 1, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_mctx_2544_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2557_, 2, v_zetaDeltaFVarIds_2545_);
lean_ctor_set(v_reuseFailAlloc_2557_, 3, v_postponed_2546_);
lean_ctor_set(v_reuseFailAlloc_2557_, 4, v_diag_2547_);
v___x_2553_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_st_ref_set(v___y_2523_, v___x_2553_);
v___x_2555_ = lean_box(0);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2585_, lean_object* v_docs_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2585_, v_docs_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2595_, lean_object* v_binders_2596_, lean_object* v_docComment_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___x_2632_; lean_object* v_env_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_st_ref_get(v_a_2603_);
v_env_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_ref(v_env_2633_);
lean_dec(v___x_2632_);
v___x_2634_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2633_, v_declName_2595_);
lean_dec_ref(v_env_2633_);
if (lean_obj_tag(v___x_2634_) == 0)
{
v___y_2606_ = v_a_2598_;
v___y_2607_ = v_a_2599_;
v___y_2608_ = v_a_2600_;
v___y_2609_ = v_a_2601_;
v___y_2610_ = v_a_2602_;
v___y_2611_ = v_a_2603_;
goto v___jp_2605_;
}
else
{
lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_docComment_2597_);
lean_dec(v_binders_2596_);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2634_, 0);
lean_dec(v_unused_2650_);
v___x_2636_ = v___x_2634_;
v_isShared_2637_ = v_isSharedCheck_2649_;
goto v_resetjp_2635_;
}
else
{
lean_dec(v___x_2634_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2649_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2638_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2639_ = 1;
v___x_2640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2595_, v___x_2639_);
v___x_2641_ = lean_string_append(v___x_2638_, v___x_2640_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2643_ = lean_string_append(v___x_2641_, v___x_2642_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set_tag(v___x_2636_, 3);
lean_ctor_set(v___x_2636_, 0, v___x_2643_);
v___x_2645_ = v___x_2636_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = l_Lean_MessageData_ofFormat(v___x_2645_);
v___x_2647_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2646_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
return v___x_2647_;
}
}
}
v___jp_2605_:
{
lean_object* v___x_2612_; 
lean_inc(v_declName_2595_);
v___x_2612_ = l_Lean_versoDocString(v_declName_2595_, v_binders_2596_, v_docComment_2597_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_fst_2614_; lean_object* v_snd_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v_a_2613_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_snd_2615_);
lean_inc(v_fst_2614_);
lean_dec(v_a_2613_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
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
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_fst_2614_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_snd_2615_);
v___x_2620_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2595_, v___x_2620_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2621_;
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_declName_2595_);
v_a_2624_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2612_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2612_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2651_, lean_object* v_binders_2652_, lean_object* v_docComment_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_addVersoDocString(v_declName_2651_, v_binders_2652_, v_docComment_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2662_, lean_object* v_docComment_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___x_2698_; lean_object* v_env_2699_; lean_object* v___x_2700_; 
v___x_2698_ = lean_st_ref_get(v_a_2669_);
v_env_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc_ref(v_env_2699_);
lean_dec(v___x_2698_);
v___x_2700_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2699_, v_declName_2662_);
lean_dec_ref(v_env_2699_);
if (lean_obj_tag(v___x_2700_) == 0)
{
v___y_2672_ = v_a_2664_;
v___y_2673_ = v_a_2665_;
v___y_2674_ = v_a_2666_;
v___y_2675_ = v_a_2667_;
v___y_2676_ = v_a_2668_;
v___y_2677_ = v_a_2669_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_docComment_2663_);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; 
v_unused_2716_ = lean_ctor_get(v___x_2700_, 0);
lean_dec(v_unused_2716_);
v___x_2702_ = v___x_2700_;
v_isShared_2703_ = v_isSharedCheck_2715_;
goto v_resetjp_2701_;
}
else
{
lean_dec(v___x_2700_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2715_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2704_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2705_ = 1;
v___x_2706_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2662_, v___x_2705_);
v___x_2707_ = lean_string_append(v___x_2704_, v___x_2706_);
lean_dec_ref(v___x_2706_);
v___x_2708_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2709_ = lean_string_append(v___x_2707_, v___x_2708_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 3);
lean_ctor_set(v___x_2702_, 0, v___x_2709_);
v___x_2711_ = v___x_2702_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = l_Lean_MessageData_ofFormat(v___x_2711_);
v___x_2713_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2712_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
return v___x_2713_;
}
}
}
v___jp_2671_:
{
lean_object* v___x_2678_; 
lean_inc(v_declName_2662_);
v___x_2678_ = l_Lean_versoDocStringFromString(v_declName_2662_, v_docComment_2663_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2689_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v_fst_2680_ = lean_ctor_get(v_a_2679_, 0);
v_snd_2681_ = lean_ctor_get(v_a_2679_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2683_ = v_a_2679_;
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v_a_2679_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_snd_2681_);
v___x_2686_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2662_, v___x_2686_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_declName_2662_);
v_a_2690_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2678_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2678_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2717_, lean_object* v_docComment_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_addVersoDocStringFromString(v_declName_2717_, v_docComment_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2727_, lean_object* v_msgData_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
uint8_t v___x_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; 
v___x_2734_ = 2;
v___x_2735_ = 0;
v___x_2736_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2727_, v_msgData_2728_, v___x_2734_, v___x_2735_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2737_, lean_object* v_msgData_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2737_, v_msgData_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v_ref_2737_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2745_, lean_object* v_str_2746_, lean_object* v_as_2747_, size_t v_sz_2748_, size_t v_i_2749_, lean_object* v_b_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_a_2759_; uint8_t v___x_2763_; 
v___x_2763_ = lean_usize_dec_lt(v_i_2749_, v_sz_2748_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_b_2750_);
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v_start_2768_; lean_object* v_stop_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2789_; 
v_a_2765_ = lean_array_uget_borrowed(v_as_2747_, v_i_2749_);
v_fst_2766_ = lean_ctor_get(v_a_2765_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v_a_2765_, 1);
v_start_2768_ = lean_ctor_get(v_fst_2766_, 0);
v_stop_2769_ = lean_ctor_get(v_fst_2766_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_fst_2766_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2771_ = v_fst_2766_;
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_stop_2769_);
lean_inc(v_start_2768_);
lean_dec(v_fst_2766_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2789_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_box(0);
if (lean_obj_tag(v___y_2745_) == 1)
{
lean_object* v_val_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v_val_2774_ = lean_ctor_get(v___y_2745_, 0);
v___x_2775_ = lean_nat_add(v_val_2774_, v_start_2768_);
v___x_2776_ = lean_nat_add(v_val_2774_, v_stop_2769_);
v___x_2777_ = 0;
v___x_2778_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2778_, 0, v___x_2775_);
lean_ctor_set(v___x_2778_, 1, v___x_2776_);
lean_ctor_set_uint8(v___x_2778_, sizeof(void*)*2, v___x_2777_);
v___x_2779_ = lean_string_utf8_extract(v_str_2746_, v_start_2768_, v_stop_2769_);
lean_dec(v_stop_2769_);
lean_dec(v_start_2768_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set_tag(v___x_2771_, 2);
lean_ctor_set(v___x_2771_, 1, v___x_2779_);
lean_ctor_set(v___x_2771_, 0, v___x_2778_);
v___x_2781_ = v___x_2771_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_inc(v_snd_2767_);
v___x_2782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_snd_2767_);
v___x_2783_ = l_Lean_MessageData_ofFormat(v___x_2782_);
v___x_2784_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2781_, v___x_2783_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec_ref(v___x_2781_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref(v___x_2784_);
v_a_2759_ = v___x_2773_;
goto v___jp_2758_;
}
else
{
return v___x_2784_;
}
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_del_object(v___x_2771_);
lean_dec(v_stop_2769_);
lean_dec(v_start_2768_);
lean_inc(v_snd_2767_);
v___x_2786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_snd_2767_);
v___x_2787_ = l_Lean_MessageData_ofFormat(v___x_2786_);
v___x_2788_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2787_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref(v___x_2788_);
v_a_2759_ = v___x_2773_;
goto v___jp_2758_;
}
else
{
return v___x_2788_;
}
}
}
}
v___jp_2758_:
{
size_t v___x_2760_; size_t v___x_2761_; 
v___x_2760_ = ((size_t)1ULL);
v___x_2761_ = lean_usize_add(v_i_2749_, v___x_2760_);
v_i_2749_ = v___x_2761_;
v_b_2750_ = v_a_2759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2790_, lean_object* v_str_2791_, lean_object* v_as_2792_, lean_object* v_sz_2793_, lean_object* v_i_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
size_t v_sz_boxed_2803_; size_t v_i_boxed_2804_; lean_object* v_res_2805_; 
v_sz_boxed_2803_ = lean_unbox_usize(v_sz_2793_);
lean_dec(v_sz_2793_);
v_i_boxed_2804_ = lean_unbox_usize(v_i_2794_);
lean_dec(v_i_2794_);
v_res_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2790_, v_str_2791_, v_as_2792_, v_sz_boxed_2803_, v_i_boxed_2804_, v_b_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_as_2792_);
lean_dec_ref(v_str_2791_);
lean_dec(v___y_2790_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_str_2814_; lean_object* v___y_2816_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v_str_2814_ = l_Lean_TSyntax_getDocString(v_docstring_2806_);
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = l_Lean_Syntax_getArg(v_docstring_2806_, v___x_2831_);
v___x_2833_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2832_);
lean_dec(v___x_2832_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_box(0);
v___y_2816_ = v___x_2834_;
goto v___jp_2815_;
}
else
{
lean_object* v_val_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; 
v_val_2835_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_val_2835_);
lean_dec_ref(v___x_2833_);
v___x_2836_ = 0;
v___x_2837_ = l_Lean_SourceInfo_getPos_x3f(v_val_2835_, v___x_2836_);
lean_dec(v_val_2835_);
v___y_2816_ = v___x_2837_;
goto v___jp_2815_;
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v_fst_2818_; lean_object* v___x_2819_; size_t v_sz_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
lean_inc_ref(v_str_2814_);
v___x_2817_ = l_Lean_rewriteManualLinksCore(v_str_2814_);
v_fst_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_fst_2818_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = lean_box(0);
v_sz_2820_ = lean_array_size(v_fst_2818_);
v___x_2821_ = ((size_t)0ULL);
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2816_, v_str_2814_, v_fst_2818_, v_sz_2820_, v___x_2821_, v___x_2819_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
lean_dec(v_fst_2818_);
lean_dec_ref(v_str_2814_);
lean_dec(v___y_2816_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v___x_2822_, 0);
lean_dec(v_unused_2830_);
v___x_2824_ = v___x_2822_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_dec(v___x_2822_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2819_);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2819_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
return v___x_2822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v_docstring_2838_);
return v_res_2846_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2849_ = l_Lean_stringToMessageData(v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_val_2865_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
v___x_2873_ = l_Lean_Syntax_getArg(v_stx_2850_, v___x_2872_);
switch(lean_obj_tag(v___x_2873_))
{
case 2:
{
lean_object* v_val_2874_; 
lean_dec(v_stx_2850_);
v_val_2874_ = lean_ctor_get(v___x_2873_, 1);
lean_inc_ref(v_val_2874_);
lean_dec_ref(v___x_2873_);
v_val_2865_ = v_val_2874_;
goto v___jp_2864_;
}
case 1:
{
lean_object* v_kind_2875_; 
v_kind_2875_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_kind_2875_);
if (lean_obj_tag(v_kind_2875_) == 1)
{
lean_object* v_pre_2876_; 
v_pre_2876_ = lean_ctor_get(v_kind_2875_, 0);
lean_inc(v_pre_2876_);
if (lean_obj_tag(v_pre_2876_) == 1)
{
lean_object* v_pre_2877_; 
v_pre_2877_ = lean_ctor_get(v_pre_2876_, 0);
lean_inc(v_pre_2877_);
if (lean_obj_tag(v_pre_2877_) == 1)
{
lean_object* v_pre_2878_; 
v_pre_2878_ = lean_ctor_get(v_pre_2877_, 0);
lean_inc(v_pre_2878_);
if (lean_obj_tag(v_pre_2878_) == 1)
{
lean_object* v_pre_2879_; 
v_pre_2879_ = lean_ctor_get(v_pre_2878_, 0);
if (lean_obj_tag(v_pre_2879_) == 0)
{
lean_object* v_str_2880_; lean_object* v_str_2881_; lean_object* v_str_2882_; lean_object* v_str_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_str_2880_ = lean_ctor_get(v_kind_2875_, 1);
lean_inc_ref(v_str_2880_);
lean_dec_ref(v_kind_2875_);
v_str_2881_ = lean_ctor_get(v_pre_2876_, 1);
lean_inc_ref(v_str_2881_);
lean_dec_ref(v_pre_2876_);
v_str_2882_ = lean_ctor_get(v_pre_2877_, 1);
lean_inc_ref(v_str_2882_);
lean_dec_ref(v_pre_2877_);
v_str_2883_ = lean_ctor_get(v_pre_2878_, 1);
lean_inc_ref(v_str_2883_);
lean_dec_ref(v_pre_2878_);
v___x_2884_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2885_ = lean_string_dec_eq(v_str_2883_, v___x_2884_);
lean_dec_ref(v_str_2883_);
if (v___x_2885_ == 0)
{
lean_dec_ref(v_str_2882_);
lean_dec_ref(v_str_2881_);
lean_dec_ref(v_str_2880_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
else
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2887_ = lean_string_dec_eq(v_str_2882_, v___x_2886_);
lean_dec_ref(v_str_2882_);
if (v___x_2887_ == 0)
{
lean_dec_ref(v_str_2881_);
lean_dec_ref(v_str_2880_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
else
{
lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2888_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2889_ = lean_string_dec_eq(v_str_2881_, v___x_2888_);
lean_dec_ref(v_str_2881_);
if (v___x_2889_ == 0)
{
lean_dec_ref(v_str_2880_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
else
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2891_ = lean_string_dec_eq(v_str_2880_, v___x_2890_);
lean_dec_ref(v_str_2880_);
if (v___x_2891_ == 0)
{
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
else
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = l_Lean_Syntax_getArg(v___x_2873_, v___x_2892_);
lean_dec_ref(v___x_2873_);
if (lean_obj_tag(v___x_2893_) == 2)
{
lean_object* v_val_2894_; 
lean_dec(v_stx_2850_);
v_val_2894_ = lean_ctor_get(v___x_2893_, 1);
lean_inc_ref(v_val_2894_);
lean_dec_ref(v___x_2893_);
v_val_2865_ = v_val_2894_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec(v___x_2893_);
v___x_2895_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2850_);
v___x_2896_ = l_Lean_MessageData_ofSyntax(v_stx_2850_);
v___x_2897_ = l_Lean_indentD(v___x_2896_);
v___x_2898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2895_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2850_, v___x_2898_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v_stx_2850_);
return v___x_2899_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2878_);
lean_dec_ref(v_pre_2877_);
lean_dec_ref(v_pre_2876_);
lean_dec_ref(v_kind_2875_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
}
else
{
lean_dec(v_pre_2878_);
lean_dec_ref(v_pre_2877_);
lean_dec_ref(v_pre_2876_);
lean_dec_ref(v_kind_2875_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
}
else
{
lean_dec_ref(v_pre_2876_);
lean_dec(v_pre_2877_);
lean_dec_ref(v_kind_2875_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
}
else
{
lean_dec_ref(v_kind_2875_);
lean_dec(v_pre_2876_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
}
else
{
lean_dec(v_kind_2875_);
lean_dec_ref(v___x_2873_);
goto v___jp_2858_;
}
}
default: 
{
lean_dec(v___x_2873_);
goto v___jp_2858_;
}
}
v___jp_2858_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2859_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2850_);
v___x_2860_ = l_Lean_MessageData_ofSyntax(v_stx_2850_);
v___x_2861_ = l_Lean_indentD(v___x_2860_);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2859_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2850_, v___x_2862_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v_stx_2850_);
return v___x_2863_;
}
v___jp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = lean_string_utf8_byte_size(v_val_2865_);
v___x_2868_ = lean_unsigned_to_nat(2u);
v___x_2869_ = lean_nat_sub(v___x_2867_, v___x_2868_);
v___x_2870_ = lean_string_utf8_extract(v_val_2865_, v___x_2866_, v___x_2869_);
lean_dec(v___x_2869_);
lean_dec_ref(v_val_2865_);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2909_, lean_object* v_docComment_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; uint8_t v___x_2981_; 
v___x_2981_ = l_Lean_Name_isAnonymous(v_declName_2909_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v_env_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_st_ref_get(v___y_2916_);
v_env_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc_ref(v_env_2983_);
lean_dec(v___x_2982_);
v___x_2984_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2983_, v_declName_2909_);
lean_dec_ref(v_env_2983_);
if (lean_obj_tag(v___x_2984_) == 0)
{
v___y_2919_ = v___y_2911_;
v___y_2920_ = v___y_2912_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
goto v___jp_2918_;
}
else
{
lean_dec_ref(v___x_2984_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
lean_dec(v_docComment_2910_);
v___x_2985_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2986_ = l_Lean_MessageData_ofConstName(v_declName_2909_, v___x_2981_);
v___x_2987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2987_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2989_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2990_;
}
else
{
v___y_2919_ = v___y_2911_;
v___y_2920_ = v___y_2912_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
goto v___jp_2918_;
}
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec(v_docComment_2910_);
lean_dec(v_declName_2909_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
v___jp_2918_:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2910_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v___x_2926_; 
lean_dec_ref(v___x_2925_);
v___x_2926_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2910_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2972_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2972_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2972_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v_nextMacroScope_2933_; lean_object* v_ngen_2934_; lean_object* v_auxDeclNGen_2935_; lean_object* v_traceState_2936_; lean_object* v_messages_2937_; lean_object* v_infoState_2938_; lean_object* v_snapshotTasks_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2970_; 
v___x_2931_ = lean_st_ref_take(v___y_2924_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
v_nextMacroScope_2933_ = lean_ctor_get(v___x_2931_, 1);
v_ngen_2934_ = lean_ctor_get(v___x_2931_, 2);
v_auxDeclNGen_2935_ = lean_ctor_get(v___x_2931_, 3);
v_traceState_2936_ = lean_ctor_get(v___x_2931_, 4);
v_messages_2937_ = lean_ctor_get(v___x_2931_, 6);
v_infoState_2938_ = lean_ctor_get(v___x_2931_, 7);
v_snapshotTasks_2939_ = lean_ctor_get(v___x_2931_, 8);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2970_ == 0)
{
lean_object* v_unused_2971_; 
v_unused_2971_ = lean_ctor_get(v___x_2931_, 5);
lean_dec(v_unused_2971_);
v___x_2941_ = v___x_2931_;
v_isShared_2942_ = v_isSharedCheck_2970_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_snapshotTasks_2939_);
lean_inc(v_infoState_2938_);
lean_inc(v_messages_2937_);
lean_inc(v_traceState_2936_);
lean_inc(v_auxDeclNGen_2935_);
lean_inc(v_ngen_2934_);
lean_inc(v_nextMacroScope_2933_);
lean_inc(v_env_2932_);
lean_dec(v___x_2931_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2970_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
v___x_2943_ = l_Lean_docStringExt;
v___x_2944_ = l_String_removeLeadingSpaces(v_a_2927_);
v___x_2945_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2943_, v_env_2932_, v_declName_2909_, v___x_2944_);
v___x_2946_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 5, v___x_2946_);
lean_ctor_set(v___x_2941_, 0, v___x_2945_);
v___x_2948_ = v___x_2941_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_nextMacroScope_2933_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_ngen_2934_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_auxDeclNGen_2935_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_traceState_2936_);
lean_ctor_set(v_reuseFailAlloc_2969_, 5, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2969_, 6, v_messages_2937_);
lean_ctor_set(v_reuseFailAlloc_2969_, 7, v_infoState_2938_);
lean_ctor_set(v_reuseFailAlloc_2969_, 8, v_snapshotTasks_2939_);
v___x_2948_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_mctx_2951_; lean_object* v_zetaDeltaFVarIds_2952_; lean_object* v_postponed_2953_; lean_object* v_diag_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2967_; 
v___x_2949_ = lean_st_ref_set(v___y_2924_, v___x_2948_);
v___x_2950_ = lean_st_ref_take(v___y_2922_);
v_mctx_2951_ = lean_ctor_get(v___x_2950_, 0);
v_zetaDeltaFVarIds_2952_ = lean_ctor_get(v___x_2950_, 2);
v_postponed_2953_ = lean_ctor_get(v___x_2950_, 3);
v_diag_2954_ = lean_ctor_get(v___x_2950_, 4);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2967_ == 0)
{
lean_object* v_unused_2968_; 
v_unused_2968_ = lean_ctor_get(v___x_2950_, 1);
lean_dec(v_unused_2968_);
v___x_2956_ = v___x_2950_;
v_isShared_2957_ = v_isSharedCheck_2967_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_diag_2954_);
lean_inc(v_postponed_2953_);
lean_inc(v_zetaDeltaFVarIds_2952_);
lean_inc(v_mctx_2951_);
lean_dec(v___x_2950_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2967_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2958_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_mctx_2951_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_zetaDeltaFVarIds_2952_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_postponed_2953_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_diag_2954_);
v___x_2960_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2961_ = lean_st_ref_set(v___y_2922_, v___x_2960_);
v___x_2962_ = lean_box(0);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2962_);
v___x_2964_ = v___x_2929_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_declName_2909_);
v_a_2973_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2926_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2926_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_dec(v_docComment_2910_);
lean_dec(v_declName_2909_);
return v___x_2925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2993_, lean_object* v_docComment_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2993_, v_docComment_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3003_, lean_object* v_declName_3004_, lean_object* v_binders_3005_, lean_object* v_docComment_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
if (v_isVerso_3003_ == 0)
{
lean_object* v___x_3014_; 
lean_dec(v_binders_3005_);
v___x_3014_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3004_, v_docComment_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_addVersoDocString(v_declName_3004_, v_binders_3005_, v_docComment_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3016_, lean_object* v_declName_3017_, lean_object* v_binders_3018_, lean_object* v_docComment_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_){
_start:
{
uint8_t v_isVerso_boxed_3027_; lean_object* v_res_3028_; 
v_isVerso_boxed_3027_ = lean_unbox(v_isVerso_3016_);
v_res_3028_ = l_Lean_addDocStringOf(v_isVerso_boxed_3027_, v_declName_3017_, v_binders_3018_, v_docComment_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3029_, lean_object* v_msgData_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3029_, v_msgData_3030_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3039_, lean_object* v_msgData_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3039_, v_msgData_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v_ref_3039_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3049_, lean_object* v_t_3050_){
_start:
{
if (lean_obj_tag(v_t_3050_) == 0)
{
lean_object* v_k_3051_; lean_object* v_v_3052_; lean_object* v_l_3053_; lean_object* v_r_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3708_; 
v_k_3051_ = lean_ctor_get(v_t_3050_, 1);
v_v_3052_ = lean_ctor_get(v_t_3050_, 2);
v_l_3053_ = lean_ctor_get(v_t_3050_, 3);
v_r_3054_ = lean_ctor_get(v_t_3050_, 4);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_t_3050_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_t_3050_, 0);
lean_dec(v_unused_3709_);
v___x_3056_ = v_t_3050_;
v_isShared_3057_ = v_isSharedCheck_3708_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_r_3054_);
lean_inc(v_l_3053_);
lean_inc(v_v_3052_);
lean_inc(v_k_3051_);
lean_dec(v_t_3050_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3708_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
uint8_t v___x_3058_; 
v___x_3058_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3049_, v_k_3051_);
switch(v___x_3058_)
{
case 0:
{
lean_object* v_impl_3059_; lean_object* v___x_3060_; 
v_impl_3059_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3049_, v_l_3053_);
v___x_3060_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3059_) == 0)
{
if (lean_obj_tag(v_r_3054_) == 0)
{
lean_object* v_size_3061_; lean_object* v_size_3062_; lean_object* v_k_3063_; lean_object* v_v_3064_; lean_object* v_l_3065_; lean_object* v_r_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v_size_3061_ = lean_ctor_get(v_impl_3059_, 0);
lean_inc(v_size_3061_);
v_size_3062_ = lean_ctor_get(v_r_3054_, 0);
v_k_3063_ = lean_ctor_get(v_r_3054_, 1);
v_v_3064_ = lean_ctor_get(v_r_3054_, 2);
v_l_3065_ = lean_ctor_get(v_r_3054_, 3);
lean_inc(v_l_3065_);
v_r_3066_ = lean_ctor_get(v_r_3054_, 4);
v___x_3067_ = lean_unsigned_to_nat(3u);
v___x_3068_ = lean_nat_mul(v___x_3067_, v_size_3061_);
v___x_3069_ = lean_nat_dec_lt(v___x_3068_, v_size_3062_);
lean_dec(v___x_3068_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
lean_dec(v_l_3065_);
v___x_3070_ = lean_nat_add(v___x_3060_, v_size_3061_);
lean_dec(v_size_3061_);
v___x_3071_ = lean_nat_add(v___x_3070_, v_size_3062_);
lean_dec(v___x_3070_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 3, v_impl_3059_);
lean_ctor_set(v___x_3056_, 0, v___x_3071_);
v___x_3073_ = v___x_3056_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v_impl_3059_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v_r_3054_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
else
{
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3138_; 
lean_inc(v_r_3066_);
lean_inc(v_v_3064_);
lean_inc(v_k_3063_);
lean_inc(v_size_3062_);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; 
v_unused_3139_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_r_3054_, 2);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_r_3054_, 1);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3143_);
v___x_3076_ = v_r_3054_;
v_isShared_3077_ = v_isSharedCheck_3138_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v_r_3054_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3138_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v_size_3078_; lean_object* v_k_3079_; lean_object* v_v_3080_; lean_object* v_l_3081_; lean_object* v_r_3082_; lean_object* v_size_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_size_3078_ = lean_ctor_get(v_l_3065_, 0);
v_k_3079_ = lean_ctor_get(v_l_3065_, 1);
v_v_3080_ = lean_ctor_get(v_l_3065_, 2);
v_l_3081_ = lean_ctor_get(v_l_3065_, 3);
v_r_3082_ = lean_ctor_get(v_l_3065_, 4);
v_size_3083_ = lean_ctor_get(v_r_3066_, 0);
v___x_3084_ = lean_unsigned_to_nat(2u);
v___x_3085_ = lean_nat_mul(v___x_3084_, v_size_3083_);
v___x_3086_ = lean_nat_dec_lt(v_size_3078_, v___x_3085_);
lean_dec(v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3114_; 
lean_inc(v_r_3082_);
lean_inc(v_l_3081_);
lean_inc(v_v_3080_);
lean_inc(v_k_3079_);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_l_3065_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; 
v_unused_3115_ = lean_ctor_get(v_l_3065_, 4);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_l_3065_, 3);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_l_3065_, 2);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_l_3065_, 1);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_l_3065_, 0);
lean_dec(v_unused_3119_);
v___x_3088_ = v_l_3065_;
v_isShared_3089_ = v_isSharedCheck_3114_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v_l_3065_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3114_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3104_; 
v___x_3090_ = lean_nat_add(v___x_3060_, v_size_3061_);
lean_dec(v_size_3061_);
v___x_3091_ = lean_nat_add(v___x_3090_, v_size_3062_);
lean_dec(v_size_3062_);
if (lean_obj_tag(v_l_3081_) == 0)
{
lean_object* v_size_3112_; 
v_size_3112_ = lean_ctor_get(v_l_3081_, 0);
lean_inc(v_size_3112_);
v___y_3104_ = v_size_3112_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3113_; 
v___x_3113_ = lean_unsigned_to_nat(0u);
v___y_3104_ = v___x_3113_;
goto v___jp_3103_;
}
v___jp_3092_:
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3096_ = lean_nat_add(v___y_3093_, v___y_3095_);
lean_dec(v___y_3095_);
lean_dec(v___y_3093_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 4, v_r_3066_);
lean_ctor_set(v___x_3088_, 3, v_r_3082_);
lean_ctor_set(v___x_3088_, 2, v_v_3064_);
lean_ctor_set(v___x_3088_, 1, v_k_3063_);
lean_ctor_set(v___x_3088_, 0, v___x_3096_);
v___x_3098_ = v___x_3088_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v_r_3082_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v_r_3066_);
v___x_3098_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
lean_object* v___x_3100_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3098_);
lean_ctor_set(v___x_3076_, 3, v___y_3094_);
lean_ctor_set(v___x_3076_, 2, v_v_3080_);
lean_ctor_set(v___x_3076_, 1, v_k_3079_);
lean_ctor_set(v___x_3076_, 0, v___x_3091_);
v___x_3100_ = v___x_3076_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_k_3079_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_v_3080_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v___y_3094_);
lean_ctor_set(v_reuseFailAlloc_3101_, 4, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
v___jp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = lean_nat_add(v___x_3090_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec(v___x_3090_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_l_3081_);
lean_ctor_set(v___x_3056_, 3, v_impl_3059_);
lean_ctor_set(v___x_3056_, 0, v___x_3105_);
v___x_3107_ = v___x_3056_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_impl_3059_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v_l_3081_);
v___x_3107_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; 
v___x_3108_ = lean_nat_add(v___x_3060_, v_size_3083_);
if (lean_obj_tag(v_r_3082_) == 0)
{
lean_object* v_size_3109_; 
v_size_3109_ = lean_ctor_get(v_r_3082_, 0);
lean_inc(v_size_3109_);
v___y_3093_ = v___x_3108_;
v___y_3094_ = v___x_3107_;
v___y_3095_ = v_size_3109_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
v___y_3093_ = v___x_3108_;
v___y_3094_ = v___x_3107_;
v___y_3095_ = v___x_3110_;
goto v___jp_3092_;
}
}
}
}
}
else
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_del_object(v___x_3056_);
v___x_3120_ = lean_nat_add(v___x_3060_, v_size_3061_);
lean_dec(v_size_3061_);
v___x_3121_ = lean_nat_add(v___x_3120_, v_size_3062_);
lean_dec(v_size_3062_);
v___x_3122_ = lean_nat_add(v___x_3120_, v_size_3078_);
lean_dec(v___x_3120_);
lean_inc_ref(v_impl_3059_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_3065_);
lean_ctor_set(v___x_3076_, 3, v_impl_3059_);
lean_ctor_set(v___x_3076_, 2, v_v_3052_);
lean_ctor_set(v___x_3076_, 1, v_k_3051_);
lean_ctor_set(v___x_3076_, 0, v___x_3122_);
v___x_3124_ = v___x_3076_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_impl_3059_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_l_3065_);
v___x_3124_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
v_isSharedCheck_3131_ = !lean_is_exclusive(v_impl_3059_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; 
v_unused_3132_ = lean_ctor_get(v_impl_3059_, 4);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_impl_3059_, 3);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_impl_3059_, 2);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_impl_3059_, 1);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_impl_3059_, 0);
lean_dec(v_unused_3136_);
v___x_3126_ = v_impl_3059_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_impl_3059_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 4, v_r_3066_);
lean_ctor_set(v___x_3126_, 3, v___x_3124_);
lean_ctor_set(v___x_3126_, 2, v_v_3064_);
lean_ctor_set(v___x_3126_, 1, v_k_3063_);
lean_ctor_set(v___x_3126_, 0, v___x_3121_);
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_k_3063_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_v_3064_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_r_3066_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v_size_3144_ = lean_ctor_get(v_impl_3059_, 0);
lean_inc(v_size_3144_);
v___x_3145_ = lean_nat_add(v___x_3060_, v_size_3144_);
lean_dec(v_size_3144_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 3, v_impl_3059_);
lean_ctor_set(v___x_3056_, 0, v___x_3145_);
v___x_3147_ = v___x_3056_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_impl_3059_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_r_3054_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
if (lean_obj_tag(v_r_3054_) == 0)
{
lean_object* v_l_3149_; 
v_l_3149_ = lean_ctor_get(v_r_3054_, 3);
lean_inc(v_l_3149_);
if (lean_obj_tag(v_l_3149_) == 0)
{
lean_object* v_r_3150_; 
v_r_3150_ = lean_ctor_get(v_r_3054_, 4);
lean_inc(v_r_3150_);
if (lean_obj_tag(v_r_3150_) == 0)
{
lean_object* v_size_3151_; lean_object* v_k_3152_; lean_object* v_v_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3166_; 
v_size_3151_ = lean_ctor_get(v_r_3054_, 0);
v_k_3152_ = lean_ctor_get(v_r_3054_, 1);
v_v_3153_ = lean_ctor_get(v_r_3054_, 2);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3167_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3168_);
v___x_3155_ = v_r_3054_;
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_v_3153_);
lean_inc(v_k_3152_);
lean_inc(v_size_3151_);
lean_dec(v_r_3054_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3166_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_size_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v_size_3157_ = lean_ctor_get(v_l_3149_, 0);
v___x_3158_ = lean_nat_add(v___x_3060_, v_size_3151_);
lean_dec(v_size_3151_);
v___x_3159_ = lean_nat_add(v___x_3060_, v_size_3157_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 4, v_l_3149_);
lean_ctor_set(v___x_3155_, 3, v_impl_3059_);
lean_ctor_set(v___x_3155_, 2, v_v_3052_);
lean_ctor_set(v___x_3155_, 1, v_k_3051_);
lean_ctor_set(v___x_3155_, 0, v___x_3159_);
v___x_3161_ = v___x_3155_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_impl_3059_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_l_3149_);
v___x_3161_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3163_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_r_3150_);
lean_ctor_set(v___x_3056_, 3, v___x_3161_);
lean_ctor_set(v___x_3056_, 2, v_v_3153_);
lean_ctor_set(v___x_3056_, 1, v_k_3152_);
lean_ctor_set(v___x_3056_, 0, v___x_3158_);
v___x_3163_ = v___x_3056_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_k_3152_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_v_3153_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v_r_3150_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
}
else
{
lean_object* v_k_3169_; lean_object* v_v_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3193_; 
v_k_3169_ = lean_ctor_get(v_r_3054_, 1);
v_v_3170_ = lean_ctor_get(v_r_3054_, 2);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; lean_object* v_unused_3195_; lean_object* v_unused_3196_; 
v_unused_3194_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3194_);
v_unused_3195_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3195_);
v_unused_3196_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3196_);
v___x_3172_ = v_r_3054_;
v_isShared_3173_ = v_isSharedCheck_3193_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_v_3170_);
lean_inc(v_k_3169_);
lean_dec(v_r_3054_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3193_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3189_; 
v_k_3174_ = lean_ctor_get(v_l_3149_, 1);
v_v_3175_ = lean_ctor_get(v_l_3149_, 2);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_l_3149_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; lean_object* v_unused_3191_; lean_object* v_unused_3192_; 
v_unused_3190_ = lean_ctor_get(v_l_3149_, 4);
lean_dec(v_unused_3190_);
v_unused_3191_ = lean_ctor_get(v_l_3149_, 3);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v_l_3149_, 0);
lean_dec(v_unused_3192_);
v___x_3177_ = v_l_3149_;
v_isShared_3178_ = v_isSharedCheck_3189_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_v_3175_);
lean_inc(v_k_3174_);
lean_dec(v_l_3149_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3189_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_unsigned_to_nat(3u);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 4, v_r_3150_);
lean_ctor_set(v___x_3177_, 3, v_r_3150_);
lean_ctor_set(v___x_3177_, 2, v_v_3052_);
lean_ctor_set(v___x_3177_, 1, v_k_3051_);
lean_ctor_set(v___x_3177_, 0, v___x_3060_);
v___x_3181_ = v___x_3177_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_r_3150_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_r_3150_);
v___x_3181_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 3, v_r_3150_);
lean_ctor_set(v___x_3172_, 0, v___x_3060_);
v___x_3183_ = v___x_3172_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_k_3169_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_v_3170_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v_r_3150_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_r_3150_);
v___x_3183_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v___x_3183_);
lean_ctor_set(v___x_3056_, 3, v___x_3181_);
lean_ctor_set(v___x_3056_, 2, v_v_3175_);
lean_ctor_set(v___x_3056_, 1, v_k_3174_);
lean_ctor_set(v___x_3056_, 0, v___x_3179_);
v___x_3185_ = v___x_3056_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_k_3174_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_v_3175_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3197_; 
v_r_3197_ = lean_ctor_get(v_r_3054_, 4);
lean_inc(v_r_3197_);
if (lean_obj_tag(v_r_3197_) == 0)
{
lean_object* v_k_3198_; lean_object* v_v_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3210_; 
v_k_3198_ = lean_ctor_get(v_r_3054_, 1);
v_v_3199_ = lean_ctor_get(v_r_3054_, 2);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3211_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3213_);
v___x_3201_ = v_r_3054_;
v_isShared_3202_ = v_isSharedCheck_3210_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_v_3199_);
lean_inc(v_k_3198_);
lean_dec(v_r_3054_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3210_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_unsigned_to_nat(3u);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 4, v_l_3149_);
lean_ctor_set(v___x_3201_, 2, v_v_3052_);
lean_ctor_set(v___x_3201_, 1, v_k_3051_);
lean_ctor_set(v___x_3201_, 0, v___x_3060_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_l_3149_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v_l_3149_);
v___x_3205_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_r_3197_);
lean_ctor_set(v___x_3056_, 3, v___x_3205_);
lean_ctor_set(v___x_3056_, 2, v_v_3199_);
lean_ctor_set(v___x_3056_, 1, v_k_3198_);
lean_ctor_set(v___x_3056_, 0, v___x_3203_);
v___x_3207_ = v___x_3056_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3198_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3199_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_r_3197_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_size_3214_; lean_object* v_k_3215_; lean_object* v_v_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3227_; 
v_size_3214_ = lean_ctor_get(v_r_3054_, 0);
v_k_3215_ = lean_ctor_get(v_r_3054_, 1);
v_v_3216_ = lean_ctor_get(v_r_3054_, 2);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; lean_object* v_unused_3229_; 
v_unused_3228_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3229_);
v___x_3218_ = v_r_3054_;
v_isShared_3219_ = v_isSharedCheck_3227_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_v_3216_);
lean_inc(v_k_3215_);
lean_inc(v_size_3214_);
lean_dec(v_r_3054_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3227_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 3, v_r_3197_);
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_size_3214_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3215_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3216_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_r_3197_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_r_3197_);
v___x_3221_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_unsigned_to_nat(2u);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v___x_3221_);
lean_ctor_set(v___x_3056_, 3, v_r_3197_);
lean_ctor_set(v___x_3056_, 0, v___x_3222_);
v___x_3224_ = v___x_3056_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_r_3197_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v___x_3221_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
else
{
lean_object* v___x_3231_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 3, v_r_3054_);
lean_ctor_set(v___x_3056_, 0, v___x_3060_);
v___x_3231_ = v___x_3056_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_r_3054_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_r_3054_);
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
case 1:
{
lean_del_object(v___x_3056_);
lean_dec(v_v_3052_);
lean_dec(v_k_3051_);
if (lean_obj_tag(v_l_3053_) == 0)
{
if (lean_obj_tag(v_r_3054_) == 0)
{
lean_object* v_size_3233_; lean_object* v_k_3234_; lean_object* v_v_3235_; lean_object* v_l_3236_; lean_object* v_r_3237_; lean_object* v_size_3238_; lean_object* v_k_3239_; lean_object* v_v_3240_; lean_object* v_l_3241_; lean_object* v_r_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_size_3233_ = lean_ctor_get(v_l_3053_, 0);
v_k_3234_ = lean_ctor_get(v_l_3053_, 1);
v_v_3235_ = lean_ctor_get(v_l_3053_, 2);
v_l_3236_ = lean_ctor_get(v_l_3053_, 3);
v_r_3237_ = lean_ctor_get(v_l_3053_, 4);
lean_inc(v_r_3237_);
v_size_3238_ = lean_ctor_get(v_r_3054_, 0);
v_k_3239_ = lean_ctor_get(v_r_3054_, 1);
v_v_3240_ = lean_ctor_get(v_r_3054_, 2);
v_l_3241_ = lean_ctor_get(v_r_3054_, 3);
lean_inc(v_l_3241_);
v_r_3242_ = lean_ctor_get(v_r_3054_, 4);
v___x_3243_ = lean_unsigned_to_nat(1u);
v___x_3244_ = lean_nat_dec_lt(v_size_3233_, v_size_3238_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3380_; 
lean_inc(v_l_3236_);
lean_inc(v_v_3235_);
lean_inc(v_k_3234_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3381_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_l_3053_, 2);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_l_3053_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3385_);
v___x_3246_ = v_l_3053_;
v_isShared_3247_ = v_isSharedCheck_3380_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v_l_3053_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3380_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v_tree_3249_; 
v___x_3248_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3234_, v_v_3235_, v_l_3236_, v_r_3237_);
v_tree_3249_ = lean_ctor_get(v___x_3248_, 2);
lean_inc(v_tree_3249_);
if (lean_obj_tag(v_tree_3249_) == 0)
{
lean_object* v_k_3250_; lean_object* v_v_3251_; lean_object* v_size_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_k_3250_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_k_3250_);
v_v_3251_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_v_3251_);
lean_dec_ref(v___x_3248_);
v_size_3252_ = lean_ctor_get(v_tree_3249_, 0);
v___x_3253_ = lean_unsigned_to_nat(3u);
v___x_3254_ = lean_nat_mul(v___x_3253_, v_size_3252_);
v___x_3255_ = lean_nat_dec_lt(v___x_3254_, v_size_3238_);
lean_dec(v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
lean_dec(v_l_3241_);
v___x_3256_ = lean_nat_add(v___x_3243_, v_size_3252_);
v___x_3257_ = lean_nat_add(v___x_3256_, v_size_3238_);
lean_dec(v___x_3256_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_r_3054_);
lean_ctor_set(v___x_3246_, 3, v_tree_3249_);
lean_ctor_set(v___x_3246_, 2, v_v_3251_);
lean_ctor_set(v___x_3246_, 1, v_k_3250_);
lean_ctor_set(v___x_3246_, 0, v___x_3257_);
v___x_3259_ = v___x_3246_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_k_3250_);
lean_ctor_set(v_reuseFailAlloc_3260_, 2, v_v_3251_);
lean_ctor_set(v_reuseFailAlloc_3260_, 3, v_tree_3249_);
lean_ctor_set(v_reuseFailAlloc_3260_, 4, v_r_3054_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
else
{
lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3315_; 
lean_inc(v_r_3242_);
lean_inc(v_v_3240_);
lean_inc(v_k_3239_);
lean_inc(v_size_3238_);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3316_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_r_3054_, 2);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_r_3054_, 1);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3320_);
v___x_3262_ = v_r_3054_;
v_isShared_3263_ = v_isSharedCheck_3315_;
goto v_resetjp_3261_;
}
else
{
lean_dec(v_r_3054_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3315_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v_size_3264_; lean_object* v_k_3265_; lean_object* v_v_3266_; lean_object* v_l_3267_; lean_object* v_r_3268_; lean_object* v_size_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_size_3264_ = lean_ctor_get(v_l_3241_, 0);
v_k_3265_ = lean_ctor_get(v_l_3241_, 1);
v_v_3266_ = lean_ctor_get(v_l_3241_, 2);
v_l_3267_ = lean_ctor_get(v_l_3241_, 3);
v_r_3268_ = lean_ctor_get(v_l_3241_, 4);
v_size_3269_ = lean_ctor_get(v_r_3242_, 0);
v___x_3270_ = lean_unsigned_to_nat(2u);
v___x_3271_ = lean_nat_mul(v___x_3270_, v_size_3269_);
v___x_3272_ = lean_nat_dec_lt(v_size_3264_, v___x_3271_);
lean_dec(v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3300_; 
lean_inc(v_r_3268_);
lean_inc(v_l_3267_);
lean_inc(v_v_3266_);
lean_inc(v_k_3265_);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_l_3241_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; 
v_unused_3301_ = lean_ctor_get(v_l_3241_, 4);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_l_3241_, 3);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3241_, 2);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_3241_, 1);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_3241_, 0);
lean_dec(v_unused_3305_);
v___x_3274_ = v_l_3241_;
v_isShared_3275_ = v_isSharedCheck_3300_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v_l_3241_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3300_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3290_; 
v___x_3276_ = lean_nat_add(v___x_3243_, v_size_3252_);
v___x_3277_ = lean_nat_add(v___x_3276_, v_size_3238_);
lean_dec(v_size_3238_);
if (lean_obj_tag(v_l_3267_) == 0)
{
lean_object* v_size_3298_; 
v_size_3298_ = lean_ctor_get(v_l_3267_, 0);
lean_inc(v_size_3298_);
v___y_3290_ = v_size_3298_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_unsigned_to_nat(0u);
v___y_3290_ = v___x_3299_;
goto v___jp_3289_;
}
v___jp_3278_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = lean_nat_add(v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec(v___y_3280_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 4, v_r_3242_);
lean_ctor_set(v___x_3274_, 3, v_r_3268_);
lean_ctor_set(v___x_3274_, 2, v_v_3240_);
lean_ctor_set(v___x_3274_, 1, v_k_3239_);
lean_ctor_set(v___x_3274_, 0, v___x_3282_);
v___x_3284_ = v___x_3274_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v_r_3268_);
lean_ctor_set(v_reuseFailAlloc_3288_, 4, v_r_3242_);
v___x_3284_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3286_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 4, v___x_3284_);
lean_ctor_set(v___x_3262_, 3, v___y_3279_);
lean_ctor_set(v___x_3262_, 2, v_v_3266_);
lean_ctor_set(v___x_3262_, 1, v_k_3265_);
lean_ctor_set(v___x_3262_, 0, v___x_3277_);
v___x_3286_ = v___x_3262_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_k_3265_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_v_3266_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v___y_3279_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v___x_3284_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
v___jp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_nat_add(v___x_3276_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec(v___x_3276_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_l_3267_);
lean_ctor_set(v___x_3246_, 3, v_tree_3249_);
lean_ctor_set(v___x_3246_, 2, v_v_3251_);
lean_ctor_set(v___x_3246_, 1, v_k_3250_);
lean_ctor_set(v___x_3246_, 0, v___x_3291_);
v___x_3293_ = v___x_3246_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_k_3250_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_v_3251_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v_tree_3249_);
lean_ctor_set(v_reuseFailAlloc_3297_, 4, v_l_3267_);
v___x_3293_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; 
v___x_3294_ = lean_nat_add(v___x_3243_, v_size_3269_);
if (lean_obj_tag(v_r_3268_) == 0)
{
lean_object* v_size_3295_; 
v_size_3295_ = lean_ctor_get(v_r_3268_, 0);
lean_inc(v_size_3295_);
v___y_3279_ = v___x_3293_;
v___y_3280_ = v___x_3294_;
v___y_3281_ = v_size_3295_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
v___y_3279_ = v___x_3293_;
v___y_3280_ = v___x_3294_;
v___y_3281_ = v___x_3296_;
goto v___jp_3278_;
}
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3310_; 
v___x_3306_ = lean_nat_add(v___x_3243_, v_size_3252_);
v___x_3307_ = lean_nat_add(v___x_3306_, v_size_3238_);
lean_dec(v_size_3238_);
v___x_3308_ = lean_nat_add(v___x_3306_, v_size_3264_);
lean_dec(v___x_3306_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 4, v_l_3241_);
lean_ctor_set(v___x_3262_, 3, v_tree_3249_);
lean_ctor_set(v___x_3262_, 2, v_v_3251_);
lean_ctor_set(v___x_3262_, 1, v_k_3250_);
lean_ctor_set(v___x_3262_, 0, v___x_3308_);
v___x_3310_ = v___x_3262_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3250_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3251_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v_tree_3249_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_l_3241_);
v___x_3310_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3312_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_r_3242_);
lean_ctor_set(v___x_3246_, 3, v___x_3310_);
lean_ctor_set(v___x_3246_, 2, v_v_3240_);
lean_ctor_set(v___x_3246_, 1, v_k_3239_);
lean_ctor_set(v___x_3246_, 0, v___x_3307_);
v___x_3312_ = v___x_3246_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_r_3242_);
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
}
else
{
lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3374_; 
lean_inc(v_r_3242_);
lean_inc(v_v_3240_);
lean_inc(v_k_3239_);
lean_inc(v_size_3238_);
v_isSharedCheck_3374_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; 
v_unused_3375_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3375_);
v_unused_3376_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_r_3054_, 2);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_r_3054_, 1);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3379_);
v___x_3322_ = v_r_3054_;
v_isShared_3323_ = v_isSharedCheck_3374_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v_r_3054_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3374_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
if (lean_obj_tag(v_l_3241_) == 0)
{
if (lean_obj_tag(v_r_3242_) == 0)
{
lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v_size_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v_k_3324_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_k_3324_);
v_v_3325_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_v_3325_);
lean_dec_ref(v___x_3248_);
v_size_3326_ = lean_ctor_get(v_l_3241_, 0);
v___x_3327_ = lean_nat_add(v___x_3243_, v_size_3238_);
lean_dec(v_size_3238_);
v___x_3328_ = lean_nat_add(v___x_3243_, v_size_3326_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 4, v_l_3241_);
lean_ctor_set(v___x_3322_, 3, v_tree_3249_);
lean_ctor_set(v___x_3322_, 2, v_v_3325_);
lean_ctor_set(v___x_3322_, 1, v_k_3324_);
lean_ctor_set(v___x_3322_, 0, v___x_3328_);
v___x_3330_ = v___x_3322_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_tree_3249_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_l_3241_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_r_3242_);
lean_ctor_set(v___x_3246_, 3, v___x_3330_);
lean_ctor_set(v___x_3246_, 2, v_v_3240_);
lean_ctor_set(v___x_3246_, 1, v_k_3239_);
lean_ctor_set(v___x_3246_, 0, v___x_3327_);
v___x_3332_ = v___x_3246_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_r_3242_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
else
{
lean_object* v_k_3335_; lean_object* v_v_3336_; lean_object* v_k_3337_; lean_object* v_v_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_size_3238_);
v_k_3335_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_k_3335_);
v_v_3336_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_v_3336_);
lean_dec_ref(v___x_3248_);
v_k_3337_ = lean_ctor_get(v_l_3241_, 1);
v_v_3338_ = lean_ctor_get(v_l_3241_, 2);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_l_3241_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; lean_object* v_unused_3354_; lean_object* v_unused_3355_; 
v_unused_3353_ = lean_ctor_get(v_l_3241_, 4);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_l_3241_, 3);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_l_3241_, 0);
lean_dec(v_unused_3355_);
v___x_3340_ = v_l_3241_;
v_isShared_3341_ = v_isSharedCheck_3352_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_v_3338_);
lean_inc(v_k_3337_);
lean_dec(v_l_3241_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3352_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3342_ = lean_unsigned_to_nat(3u);
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 4, v_r_3242_);
lean_ctor_set(v___x_3340_, 3, v_r_3242_);
lean_ctor_set(v___x_3340_, 2, v_v_3336_);
lean_ctor_set(v___x_3340_, 1, v_k_3335_);
lean_ctor_set(v___x_3340_, 0, v___x_3243_);
v___x_3344_ = v___x_3340_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_k_3335_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_v_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_r_3242_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_r_3242_);
v___x_3344_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3346_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 3, v_r_3242_);
lean_ctor_set(v___x_3322_, 0, v___x_3243_);
v___x_3346_ = v___x_3322_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_r_3242_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_r_3242_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v___x_3346_);
lean_ctor_set(v___x_3246_, 3, v___x_3344_);
lean_ctor_set(v___x_3246_, 2, v_v_3338_);
lean_ctor_set(v___x_3246_, 1, v_k_3337_);
lean_ctor_set(v___x_3246_, 0, v___x_3342_);
v___x_3348_ = v___x_3246_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3337_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3338_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3242_) == 0)
{
lean_object* v_k_3356_; lean_object* v_v_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
lean_dec(v_size_3238_);
v_k_3356_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_k_3356_);
v_v_3357_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_v_3357_);
lean_dec_ref(v___x_3248_);
v___x_3358_ = lean_unsigned_to_nat(3u);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 4, v_l_3241_);
lean_ctor_set(v___x_3322_, 2, v_v_3357_);
lean_ctor_set(v___x_3322_, 1, v_k_3356_);
lean_ctor_set(v___x_3322_, 0, v___x_3243_);
v___x_3360_ = v___x_3322_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_k_3356_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_v_3357_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_l_3241_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_l_3241_);
v___x_3360_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_r_3242_);
lean_ctor_set(v___x_3246_, 3, v___x_3360_);
lean_ctor_set(v___x_3246_, 2, v_v_3240_);
lean_ctor_set(v___x_3246_, 1, v_k_3239_);
lean_ctor_set(v___x_3246_, 0, v___x_3358_);
v___x_3362_ = v___x_3246_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3242_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_k_3365_; lean_object* v_v_3366_; lean_object* v___x_3368_; 
v_k_3365_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_k_3365_);
v_v_3366_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_v_3366_);
lean_dec_ref(v___x_3248_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 3, v_r_3242_);
v___x_3368_ = v___x_3322_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_size_3238_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_r_3242_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v_r_3242_);
v___x_3368_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_unsigned_to_nat(2u);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v___x_3368_);
lean_ctor_set(v___x_3246_, 3, v_r_3242_);
lean_ctor_set(v___x_3246_, 2, v_v_3366_);
lean_ctor_set(v___x_3246_, 1, v_k_3365_);
lean_ctor_set(v___x_3246_, 0, v___x_3369_);
v___x_3371_ = v___x_3246_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_k_3365_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_v_3366_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v_r_3242_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v___x_3368_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3538_; 
lean_inc(v_r_3242_);
lean_inc(v_v_3240_);
lean_inc(v_k_3239_);
v_isSharedCheck_3538_ = !lean_is_exclusive(v_r_3054_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; lean_object* v_unused_3540_; lean_object* v_unused_3541_; lean_object* v_unused_3542_; lean_object* v_unused_3543_; 
v_unused_3539_ = lean_ctor_get(v_r_3054_, 4);
lean_dec(v_unused_3539_);
v_unused_3540_ = lean_ctor_get(v_r_3054_, 3);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_r_3054_, 2);
lean_dec(v_unused_3541_);
v_unused_3542_ = lean_ctor_get(v_r_3054_, 1);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_r_3054_, 0);
lean_dec(v_unused_3543_);
v___x_3387_ = v_r_3054_;
v_isShared_3388_ = v_isSharedCheck_3538_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v_r_3054_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3538_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v_tree_3390_; 
v___x_3389_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3239_, v_v_3240_, v_l_3241_, v_r_3242_);
v_tree_3390_ = lean_ctor_get(v___x_3389_, 2);
lean_inc(v_tree_3390_);
if (lean_obj_tag(v_tree_3390_) == 0)
{
lean_object* v_k_3391_; lean_object* v_v_3392_; lean_object* v_size_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; uint8_t v___x_3396_; 
v_k_3391_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_k_3391_);
v_v_3392_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_v_3392_);
lean_dec_ref(v___x_3389_);
v_size_3393_ = lean_ctor_get(v_tree_3390_, 0);
v___x_3394_ = lean_unsigned_to_nat(3u);
v___x_3395_ = lean_nat_mul(v___x_3394_, v_size_3393_);
v___x_3396_ = lean_nat_dec_lt(v___x_3395_, v_size_3233_);
lean_dec(v___x_3395_);
if (v___x_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_dec(v_r_3237_);
v___x_3397_ = lean_nat_add(v___x_3243_, v_size_3233_);
v___x_3398_ = lean_nat_add(v___x_3397_, v_size_3393_);
lean_dec(v___x_3397_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_tree_3390_);
lean_ctor_set(v___x_3387_, 3, v_l_3053_);
lean_ctor_set(v___x_3387_, 2, v_v_3392_);
lean_ctor_set(v___x_3387_, 1, v_k_3391_);
lean_ctor_set(v___x_3387_, 0, v___x_3398_);
v___x_3400_ = v___x_3387_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_k_3391_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_v_3392_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3401_, 4, v_tree_3390_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
else
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3467_; 
lean_inc(v_l_3236_);
lean_inc(v_v_3235_);
lean_inc(v_k_3234_);
lean_inc(v_size_3233_);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; lean_object* v_unused_3469_; lean_object* v_unused_3470_; lean_object* v_unused_3471_; lean_object* v_unused_3472_; 
v_unused_3468_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_l_3053_, 2);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_l_3053_, 1);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3472_);
v___x_3403_ = v_l_3053_;
v_isShared_3404_ = v_isSharedCheck_3467_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v_l_3053_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3467_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v_size_3405_; lean_object* v_size_3406_; lean_object* v_k_3407_; lean_object* v_v_3408_; lean_object* v_l_3409_; lean_object* v_r_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_size_3405_ = lean_ctor_get(v_l_3236_, 0);
v_size_3406_ = lean_ctor_get(v_r_3237_, 0);
v_k_3407_ = lean_ctor_get(v_r_3237_, 1);
v_v_3408_ = lean_ctor_get(v_r_3237_, 2);
v_l_3409_ = lean_ctor_get(v_r_3237_, 3);
v_r_3410_ = lean_ctor_get(v_r_3237_, 4);
v___x_3411_ = lean_unsigned_to_nat(2u);
v___x_3412_ = lean_nat_mul(v___x_3411_, v_size_3405_);
v___x_3413_ = lean_nat_dec_lt(v_size_3406_, v___x_3412_);
lean_dec(v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3451_; 
lean_inc(v_r_3410_);
lean_inc(v_l_3409_);
lean_inc(v_v_3408_);
lean_inc(v_k_3407_);
lean_del_object(v___x_3403_);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_r_3237_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; 
v_unused_3452_ = lean_ctor_get(v_r_3237_, 4);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_r_3237_, 3);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_r_3237_, 2);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_r_3237_, 1);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_r_3237_, 0);
lean_dec(v_unused_3456_);
v___x_3415_ = v_r_3237_;
v_isShared_3416_ = v_isSharedCheck_3451_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_r_3237_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3451_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3439_; lean_object* v___y_3441_; 
v___x_3417_ = lean_nat_add(v___x_3243_, v_size_3233_);
lean_dec(v_size_3233_);
v___x_3418_ = lean_nat_add(v___x_3417_, v_size_3393_);
lean_dec(v___x_3417_);
v___x_3439_ = lean_nat_add(v___x_3243_, v_size_3405_);
if (lean_obj_tag(v_l_3409_) == 0)
{
lean_object* v_size_3449_; 
v_size_3449_ = lean_ctor_get(v_l_3409_, 0);
lean_inc(v_size_3449_);
v___y_3441_ = v_size_3449_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___y_3441_ = v___x_3450_;
goto v___jp_3440_;
}
v___jp_3419_:
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
v___x_3423_ = lean_nat_add(v___y_3420_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec(v___y_3420_);
lean_inc_ref(v_tree_3390_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 4, v_tree_3390_);
lean_ctor_set(v___x_3415_, 3, v_r_3410_);
lean_ctor_set(v___x_3415_, 2, v_v_3392_);
lean_ctor_set(v___x_3415_, 1, v_k_3391_);
lean_ctor_set(v___x_3415_, 0, v___x_3423_);
v___x_3425_ = v___x_3415_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_k_3391_);
lean_ctor_set(v_reuseFailAlloc_3438_, 2, v_v_3392_);
lean_ctor_set(v_reuseFailAlloc_3438_, 3, v_r_3410_);
lean_ctor_set(v_reuseFailAlloc_3438_, 4, v_tree_3390_);
v___x_3425_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
v_isSharedCheck_3432_ = !lean_is_exclusive(v_tree_3390_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; lean_object* v_unused_3435_; lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3433_ = lean_ctor_get(v_tree_3390_, 4);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v_tree_3390_, 3);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v_tree_3390_, 2);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_tree_3390_, 1);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_tree_3390_, 0);
lean_dec(v_unused_3437_);
v___x_3427_ = v_tree_3390_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v_tree_3390_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 4, v___x_3425_);
lean_ctor_set(v___x_3427_, 3, v___y_3421_);
lean_ctor_set(v___x_3427_, 2, v_v_3408_);
lean_ctor_set(v___x_3427_, 1, v_k_3407_);
lean_ctor_set(v___x_3427_, 0, v___x_3418_);
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3407_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3408_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v___y_3421_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v___x_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
v___jp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_nat_add(v___x_3439_, v___y_3441_);
lean_dec(v___y_3441_);
lean_dec(v___x_3439_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_l_3409_);
lean_ctor_set(v___x_3387_, 3, v_l_3236_);
lean_ctor_set(v___x_3387_, 2, v_v_3235_);
lean_ctor_set(v___x_3387_, 1, v_k_3234_);
lean_ctor_set(v___x_3387_, 0, v___x_3442_);
v___x_3444_ = v___x_3387_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_l_3409_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_nat_add(v___x_3243_, v_size_3393_);
if (lean_obj_tag(v_r_3410_) == 0)
{
lean_object* v_size_3446_; 
v_size_3446_ = lean_ctor_get(v_r_3410_, 0);
lean_inc(v_size_3446_);
v___y_3420_ = v___x_3445_;
v___y_3421_ = v___x_3444_;
v___y_3422_ = v_size_3446_;
goto v___jp_3419_;
}
else
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___y_3420_ = v___x_3445_;
v___y_3421_ = v___x_3444_;
v___y_3422_ = v___x_3447_;
goto v___jp_3419_;
}
}
}
}
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3457_ = lean_nat_add(v___x_3243_, v_size_3233_);
lean_dec(v_size_3233_);
v___x_3458_ = lean_nat_add(v___x_3457_, v_size_3393_);
lean_dec(v___x_3457_);
v___x_3459_ = lean_nat_add(v___x_3243_, v_size_3393_);
v___x_3460_ = lean_nat_add(v___x_3459_, v_size_3406_);
lean_dec(v___x_3459_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_tree_3390_);
lean_ctor_set(v___x_3387_, 3, v_r_3237_);
lean_ctor_set(v___x_3387_, 2, v_v_3392_);
lean_ctor_set(v___x_3387_, 1, v_k_3391_);
lean_ctor_set(v___x_3387_, 0, v___x_3460_);
v___x_3462_ = v___x_3387_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_k_3391_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_v_3392_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v_r_3237_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v_tree_3390_);
v___x_3462_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3464_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 4, v___x_3462_);
lean_ctor_set(v___x_3403_, 0, v___x_3458_);
v___x_3464_ = v___x_3403_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3236_) == 0)
{
lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3496_; 
lean_inc_ref(v_l_3236_);
lean_inc(v_v_3235_);
lean_inc(v_k_3234_);
lean_inc(v_size_3233_);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; lean_object* v_unused_3501_; 
v_unused_3497_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3497_);
v_unused_3498_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_l_3053_, 2);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_l_3053_, 1);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3501_);
v___x_3474_ = v_l_3053_;
v_isShared_3475_ = v_isSharedCheck_3496_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v_l_3053_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3496_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
if (lean_obj_tag(v_r_3237_) == 0)
{
lean_object* v_k_3476_; lean_object* v_v_3477_; lean_object* v_size_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_k_3476_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_k_3476_);
v_v_3477_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_v_3477_);
lean_dec_ref(v___x_3389_);
v_size_3478_ = lean_ctor_get(v_r_3237_, 0);
v___x_3479_ = lean_nat_add(v___x_3243_, v_size_3233_);
lean_dec(v_size_3233_);
v___x_3480_ = lean_nat_add(v___x_3243_, v_size_3478_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_tree_3390_);
lean_ctor_set(v___x_3387_, 3, v_r_3237_);
lean_ctor_set(v___x_3387_, 2, v_v_3477_);
lean_ctor_set(v___x_3387_, 1, v_k_3476_);
lean_ctor_set(v___x_3387_, 0, v___x_3480_);
v___x_3482_ = v___x_3387_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_r_3237_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_tree_3390_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 4, v___x_3482_);
lean_ctor_set(v___x_3474_, 0, v___x_3479_);
v___x_3484_ = v___x_3474_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
else
{
lean_object* v_k_3487_; lean_object* v_v_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v_size_3233_);
v_k_3487_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_k_3487_);
v_v_3488_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_v_3488_);
lean_dec_ref(v___x_3389_);
v___x_3489_ = lean_unsigned_to_nat(3u);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_r_3237_);
lean_ctor_set(v___x_3387_, 3, v_r_3237_);
lean_ctor_set(v___x_3387_, 2, v_v_3488_);
lean_ctor_set(v___x_3387_, 1, v_k_3487_);
lean_ctor_set(v___x_3387_, 0, v___x_3243_);
v___x_3491_ = v___x_3387_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_r_3237_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_r_3237_);
v___x_3491_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3493_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 4, v___x_3491_);
lean_ctor_set(v___x_3474_, 0, v___x_3489_);
v___x_3493_ = v___x_3474_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3494_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3237_) == 0)
{
lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3526_; 
lean_inc(v_l_3236_);
lean_inc(v_v_3235_);
lean_inc(v_k_3234_);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; lean_object* v_unused_3528_; lean_object* v_unused_3529_; lean_object* v_unused_3530_; lean_object* v_unused_3531_; 
v_unused_3527_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_l_3053_, 2);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_l_3053_, 1);
lean_dec(v_unused_3530_);
v_unused_3531_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3531_);
v___x_3503_ = v_l_3053_;
v_isShared_3504_ = v_isSharedCheck_3526_;
goto v_resetjp_3502_;
}
else
{
lean_dec(v_l_3053_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3526_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v_k_3505_; lean_object* v_v_3506_; lean_object* v_k_3507_; lean_object* v_v_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3522_; 
v_k_3505_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_k_3505_);
v_v_3506_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_v_3506_);
lean_dec_ref(v___x_3389_);
v_k_3507_ = lean_ctor_get(v_r_3237_, 1);
v_v_3508_ = lean_ctor_get(v_r_3237_, 2);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_r_3237_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; lean_object* v_unused_3524_; lean_object* v_unused_3525_; 
v_unused_3523_ = lean_ctor_get(v_r_3237_, 4);
lean_dec(v_unused_3523_);
v_unused_3524_ = lean_ctor_get(v_r_3237_, 3);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_r_3237_, 0);
lean_dec(v_unused_3525_);
v___x_3510_ = v_r_3237_;
v_isShared_3511_ = v_isSharedCheck_3522_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_v_3508_);
lean_inc(v_k_3507_);
lean_dec(v_r_3237_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3522_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3512_ = lean_unsigned_to_nat(3u);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 4, v_l_3236_);
lean_ctor_set(v___x_3510_, 3, v_l_3236_);
lean_ctor_set(v___x_3510_, 2, v_v_3235_);
lean_ctor_set(v___x_3510_, 1, v_k_3234_);
lean_ctor_set(v___x_3510_, 0, v___x_3243_);
v___x_3514_ = v___x_3510_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_l_3236_);
v___x_3514_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3516_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_l_3236_);
lean_ctor_set(v___x_3387_, 3, v_l_3236_);
lean_ctor_set(v___x_3387_, 2, v_v_3506_);
lean_ctor_set(v___x_3387_, 1, v_k_3505_);
lean_ctor_set(v___x_3387_, 0, v___x_3243_);
v___x_3516_ = v___x_3387_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_k_3505_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_v_3506_);
lean_ctor_set(v_reuseFailAlloc_3520_, 3, v_l_3236_);
lean_ctor_set(v_reuseFailAlloc_3520_, 4, v_l_3236_);
v___x_3516_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 4, v___x_3516_);
lean_ctor_set(v___x_3503_, 3, v___x_3514_);
lean_ctor_set(v___x_3503_, 2, v_v_3508_);
lean_ctor_set(v___x_3503_, 1, v_k_3507_);
lean_ctor_set(v___x_3503_, 0, v___x_3512_);
v___x_3518_ = v___x_3503_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3507_);
lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3508_);
lean_ctor_set(v_reuseFailAlloc_3519_, 3, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3519_, 4, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
else
{
lean_object* v_k_3532_; lean_object* v_v_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v_k_3532_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_k_3532_);
v_v_3533_ = lean_ctor_get(v___x_3389_, 1);
lean_inc(v_v_3533_);
lean_dec_ref(v___x_3389_);
v___x_3534_ = lean_unsigned_to_nat(2u);
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_r_3237_);
lean_ctor_set(v___x_3387_, 3, v_l_3053_);
lean_ctor_set(v___x_3387_, 2, v_v_3533_);
lean_ctor_set(v___x_3387_, 1, v_k_3532_);
lean_ctor_set(v___x_3387_, 0, v___x_3534_);
v___x_3536_ = v___x_3387_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3532_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3533_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_r_3237_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
}
}
else
{
return v_l_3053_;
}
}
else
{
return v_r_3054_;
}
}
default: 
{
lean_object* v_impl_3544_; lean_object* v___x_3545_; 
v_impl_3544_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3049_, v_r_3054_);
v___x_3545_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3544_) == 0)
{
if (lean_obj_tag(v_l_3053_) == 0)
{
lean_object* v_size_3546_; lean_object* v_size_3547_; lean_object* v_k_3548_; lean_object* v_v_3549_; lean_object* v_l_3550_; lean_object* v_r_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_size_3546_ = lean_ctor_get(v_impl_3544_, 0);
lean_inc(v_size_3546_);
v_size_3547_ = lean_ctor_get(v_l_3053_, 0);
v_k_3548_ = lean_ctor_get(v_l_3053_, 1);
v_v_3549_ = lean_ctor_get(v_l_3053_, 2);
v_l_3550_ = lean_ctor_get(v_l_3053_, 3);
v_r_3551_ = lean_ctor_get(v_l_3053_, 4);
lean_inc(v_r_3551_);
v___x_3552_ = lean_unsigned_to_nat(3u);
v___x_3553_ = lean_nat_mul(v___x_3552_, v_size_3546_);
v___x_3554_ = lean_nat_dec_lt(v___x_3553_, v_size_3547_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec(v_r_3551_);
v___x_3555_ = lean_nat_add(v___x_3545_, v_size_3547_);
v___x_3556_ = lean_nat_add(v___x_3555_, v_size_3546_);
lean_dec(v_size_3546_);
lean_dec(v___x_3555_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_impl_3544_);
lean_ctor_set(v___x_3056_, 0, v___x_3556_);
v___x_3558_ = v___x_3056_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3559_, 4, v_impl_3544_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3625_; 
lean_inc(v_l_3550_);
lean_inc(v_v_3549_);
lean_inc(v_k_3548_);
lean_inc(v_size_3547_);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3626_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_l_3053_, 2);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_l_3053_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3630_);
v___x_3561_ = v_l_3053_;
v_isShared_3562_ = v_isSharedCheck_3625_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v_l_3053_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3625_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_size_3563_; lean_object* v_size_3564_; lean_object* v_k_3565_; lean_object* v_v_3566_; lean_object* v_l_3567_; lean_object* v_r_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_size_3563_ = lean_ctor_get(v_l_3550_, 0);
v_size_3564_ = lean_ctor_get(v_r_3551_, 0);
v_k_3565_ = lean_ctor_get(v_r_3551_, 1);
v_v_3566_ = lean_ctor_get(v_r_3551_, 2);
v_l_3567_ = lean_ctor_get(v_r_3551_, 3);
v_r_3568_ = lean_ctor_get(v_r_3551_, 4);
v___x_3569_ = lean_unsigned_to_nat(2u);
v___x_3570_ = lean_nat_mul(v___x_3569_, v_size_3563_);
v___x_3571_ = lean_nat_dec_lt(v_size_3564_, v___x_3570_);
lean_dec(v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3600_; 
lean_inc(v_r_3568_);
lean_inc(v_l_3567_);
lean_inc(v_v_3566_);
lean_inc(v_k_3565_);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_r_3551_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; 
v_unused_3601_ = lean_ctor_get(v_r_3551_, 4);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v_r_3551_, 3);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_r_3551_, 2);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_r_3551_, 1);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_r_3551_, 0);
lean_dec(v_unused_3605_);
v___x_3573_ = v_r_3551_;
v_isShared_3574_ = v_isSharedCheck_3600_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v_r_3551_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3600_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___x_3588_; lean_object* v___y_3590_; 
v___x_3575_ = lean_nat_add(v___x_3545_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3576_ = lean_nat_add(v___x_3575_, v_size_3546_);
lean_dec(v___x_3575_);
v___x_3588_ = lean_nat_add(v___x_3545_, v_size_3563_);
if (lean_obj_tag(v_l_3567_) == 0)
{
lean_object* v_size_3598_; 
v_size_3598_ = lean_ctor_get(v_l_3567_, 0);
lean_inc(v_size_3598_);
v___y_3590_ = v_size_3598_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___y_3590_ = v___x_3599_;
goto v___jp_3589_;
}
v___jp_3577_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_nat_add(v___y_3579_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec(v___y_3579_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 4, v_impl_3544_);
lean_ctor_set(v___x_3573_, 3, v_r_3568_);
lean_ctor_set(v___x_3573_, 2, v_v_3052_);
lean_ctor_set(v___x_3573_, 1, v_k_3051_);
lean_ctor_set(v___x_3573_, 0, v___x_3581_);
v___x_3583_ = v___x_3573_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_r_3568_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_impl_3544_);
v___x_3583_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v___x_3583_);
lean_ctor_set(v___x_3561_, 3, v___y_3578_);
lean_ctor_set(v___x_3561_, 2, v_v_3566_);
lean_ctor_set(v___x_3561_, 1, v_k_3565_);
lean_ctor_set(v___x_3561_, 0, v___x_3576_);
v___x_3585_ = v___x_3561_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_k_3565_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_v_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v___y_3578_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
v___jp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_nat_add(v___x_3588_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec(v___x_3588_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_l_3567_);
lean_ctor_set(v___x_3056_, 3, v_l_3550_);
lean_ctor_set(v___x_3056_, 2, v_v_3549_);
lean_ctor_set(v___x_3056_, 1, v_k_3548_);
lean_ctor_set(v___x_3056_, 0, v___x_3591_);
v___x_3593_ = v___x_3056_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_k_3548_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_v_3549_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_l_3550_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_l_3567_);
v___x_3593_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; 
v___x_3594_ = lean_nat_add(v___x_3545_, v_size_3546_);
lean_dec(v_size_3546_);
if (lean_obj_tag(v_r_3568_) == 0)
{
lean_object* v_size_3595_; 
v_size_3595_ = lean_ctor_get(v_r_3568_, 0);
lean_inc(v_size_3595_);
v___y_3578_ = v___x_3593_;
v___y_3579_ = v___x_3594_;
v___y_3580_ = v_size_3595_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_unsigned_to_nat(0u);
v___y_3578_ = v___x_3593_;
v___y_3579_ = v___x_3594_;
v___y_3580_ = v___x_3596_;
goto v___jp_3577_;
}
}
}
}
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_del_object(v___x_3056_);
v___x_3606_ = lean_nat_add(v___x_3545_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3607_ = lean_nat_add(v___x_3606_, v_size_3546_);
lean_dec(v___x_3606_);
v___x_3608_ = lean_nat_add(v___x_3545_, v_size_3546_);
lean_dec(v_size_3546_);
v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3564_);
lean_dec(v___x_3608_);
lean_inc_ref(v_impl_3544_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v_impl_3544_);
lean_ctor_set(v___x_3561_, 3, v_r_3551_);
lean_ctor_set(v___x_3561_, 2, v_v_3052_);
lean_ctor_set(v___x_3561_, 1, v_k_3051_);
lean_ctor_set(v___x_3561_, 0, v___x_3609_);
v___x_3611_ = v___x_3561_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_r_3551_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_impl_3544_);
v___x_3611_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_isSharedCheck_3618_ = !lean_is_exclusive(v_impl_3544_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3619_ = lean_ctor_get(v_impl_3544_, 4);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v_impl_3544_, 3);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_impl_3544_, 2);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_impl_3544_, 1);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_impl_3544_, 0);
lean_dec(v_unused_3623_);
v___x_3613_ = v_impl_3544_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_dec(v_impl_3544_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 4, v___x_3611_);
lean_ctor_set(v___x_3613_, 3, v_l_3550_);
lean_ctor_set(v___x_3613_, 2, v_v_3549_);
lean_ctor_set(v___x_3613_, 1, v_k_3548_);
lean_ctor_set(v___x_3613_, 0, v___x_3607_);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3548_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3549_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_l_3550_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v___x_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
v_size_3631_ = lean_ctor_get(v_impl_3544_, 0);
lean_inc(v_size_3631_);
v___x_3632_ = lean_nat_add(v___x_3545_, v_size_3631_);
lean_dec(v_size_3631_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_impl_3544_);
lean_ctor_set(v___x_3056_, 0, v___x_3632_);
v___x_3634_ = v___x_3056_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_impl_3544_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
if (lean_obj_tag(v_l_3053_) == 0)
{
lean_object* v_l_3636_; 
v_l_3636_ = lean_ctor_get(v_l_3053_, 3);
if (lean_obj_tag(v_l_3636_) == 0)
{
lean_object* v_r_3637_; 
lean_inc_ref(v_l_3636_);
v_r_3637_ = lean_ctor_get(v_l_3053_, 4);
lean_inc(v_r_3637_);
if (lean_obj_tag(v_r_3637_) == 0)
{
lean_object* v_size_3638_; lean_object* v_k_3639_; lean_object* v_v_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3653_; 
v_size_3638_ = lean_ctor_get(v_l_3053_, 0);
v_k_3639_ = lean_ctor_get(v_l_3053_, 1);
v_v_3640_ = lean_ctor_get(v_l_3053_, 2);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; lean_object* v_unused_3655_; 
v_unused_3654_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3655_);
v___x_3642_ = v_l_3053_;
v_isShared_3643_ = v_isSharedCheck_3653_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_v_3640_);
lean_inc(v_k_3639_);
lean_inc(v_size_3638_);
lean_dec(v_l_3053_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3653_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v_size_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v_size_3644_ = lean_ctor_get(v_r_3637_, 0);
v___x_3645_ = lean_nat_add(v___x_3545_, v_size_3638_);
lean_dec(v_size_3638_);
v___x_3646_ = lean_nat_add(v___x_3545_, v_size_3644_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 4, v_impl_3544_);
lean_ctor_set(v___x_3642_, 3, v_r_3637_);
lean_ctor_set(v___x_3642_, 2, v_v_3052_);
lean_ctor_set(v___x_3642_, 1, v_k_3051_);
lean_ctor_set(v___x_3642_, 0, v___x_3646_);
v___x_3648_ = v___x_3642_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_r_3637_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v_impl_3544_);
v___x_3648_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v___x_3648_);
lean_ctor_set(v___x_3056_, 3, v_l_3636_);
lean_ctor_set(v___x_3056_, 2, v_v_3640_);
lean_ctor_set(v___x_3056_, 1, v_k_3639_);
lean_ctor_set(v___x_3056_, 0, v___x_3645_);
v___x_3650_ = v___x_3056_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3639_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3640_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_l_3636_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
else
{
lean_object* v_k_3656_; lean_object* v_v_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3668_; 
v_k_3656_ = lean_ctor_get(v_l_3053_, 1);
v_v_3657_ = lean_ctor_get(v_l_3053_, 2);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; lean_object* v_unused_3670_; lean_object* v_unused_3671_; 
v_unused_3669_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3669_);
v_unused_3670_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3671_);
v___x_3659_ = v_l_3053_;
v_isShared_3660_ = v_isSharedCheck_3668_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_v_3657_);
lean_inc(v_k_3656_);
lean_dec(v_l_3053_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3668_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_unsigned_to_nat(3u);
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 3, v_r_3637_);
lean_ctor_set(v___x_3659_, 2, v_v_3052_);
lean_ctor_set(v___x_3659_, 1, v_k_3051_);
lean_ctor_set(v___x_3659_, 0, v___x_3545_);
v___x_3663_ = v___x_3659_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_r_3637_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_r_3637_);
v___x_3663_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v___x_3663_);
lean_ctor_set(v___x_3056_, 3, v_l_3636_);
lean_ctor_set(v___x_3056_, 2, v_v_3657_);
lean_ctor_set(v___x_3056_, 1, v_k_3656_);
lean_ctor_set(v___x_3056_, 0, v___x_3661_);
v___x_3665_ = v___x_3056_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3656_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3657_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_l_3636_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
else
{
lean_object* v_r_3672_; 
v_r_3672_ = lean_ctor_get(v_l_3053_, 4);
lean_inc(v_r_3672_);
if (lean_obj_tag(v_r_3672_) == 0)
{
lean_object* v_k_3673_; lean_object* v_v_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3697_; 
lean_inc(v_l_3636_);
v_k_3673_ = lean_ctor_get(v_l_3053_, 1);
v_v_3674_ = lean_ctor_get(v_l_3053_, 2);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_l_3053_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3698_ = lean_ctor_get(v_l_3053_, 4);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_l_3053_, 3);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_l_3053_, 0);
lean_dec(v_unused_3700_);
v___x_3676_ = v_l_3053_;
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_v_3674_);
lean_inc(v_k_3673_);
lean_dec(v_l_3053_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3693_; 
v_k_3678_ = lean_ctor_get(v_r_3672_, 1);
v_v_3679_ = lean_ctor_get(v_r_3672_, 2);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_r_3672_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; 
v_unused_3694_ = lean_ctor_get(v_r_3672_, 4);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_r_3672_, 3);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_r_3672_, 0);
lean_dec(v_unused_3696_);
v___x_3681_ = v_r_3672_;
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_v_3679_);
lean_inc(v_k_3678_);
lean_dec(v_r_3672_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3693_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = lean_unsigned_to_nat(3u);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 4, v_l_3636_);
lean_ctor_set(v___x_3681_, 3, v_l_3636_);
lean_ctor_set(v___x_3681_, 2, v_v_3674_);
lean_ctor_set(v___x_3681_, 1, v_k_3673_);
lean_ctor_set(v___x_3681_, 0, v___x_3545_);
v___x_3685_ = v___x_3681_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_k_3673_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_v_3674_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_l_3636_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_l_3636_);
v___x_3685_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 4, v_l_3636_);
lean_ctor_set(v___x_3676_, 2, v_v_3052_);
lean_ctor_set(v___x_3676_, 1, v_k_3051_);
lean_ctor_set(v___x_3676_, 0, v___x_3545_);
v___x_3687_ = v___x_3676_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v_l_3636_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v_l_3636_);
v___x_3687_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3689_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v___x_3687_);
lean_ctor_set(v___x_3056_, 3, v___x_3685_);
lean_ctor_set(v___x_3056_, 2, v_v_3679_);
lean_ctor_set(v___x_3056_, 1, v_k_3678_);
lean_ctor_set(v___x_3056_, 0, v___x_3683_);
v___x_3689_ = v___x_3056_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3690_, 4, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3701_ = lean_unsigned_to_nat(2u);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_r_3672_);
lean_ctor_set(v___x_3056_, 0, v___x_3701_);
v___x_3703_ = v___x_3056_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_r_3672_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v___x_3706_; 
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_l_3053_);
lean_ctor_set(v___x_3056_, 0, v___x_3545_);
v___x_3706_ = v___x_3056_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3051_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3052_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_l_3053_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_l_3053_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
}
else
{
return v_t_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3710_, lean_object* v_t_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3710_, v_t_3711_);
lean_dec(v_k_3710_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3713_, lean_object* v_x_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3713_, v_x_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3716_, lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3716_, v_x_3717_);
lean_dec(v_declName_3716_);
return v_res_3718_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3721_ = l_Lean_stringToMessageData(v___x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v_env_3731_; lean_object* v___f_3732_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___x_3776_; 
v___x_3730_ = lean_st_ref_get(v___y_3728_);
v_env_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc_ref(v_env_3731_);
lean_dec(v___x_3730_);
lean_inc(v_declName_3722_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3732_, 0, v_declName_3722_);
v___x_3776_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3731_, v_declName_3722_);
lean_dec_ref(v_env_3731_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec(v_declName_3722_);
v___y_3734_ = v___y_3726_;
v___y_3735_ = v___y_3728_;
goto v___jp_3733_;
}
else
{
uint8_t v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v___f_3732_);
v___x_3777_ = 0;
v___x_3778_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3779_ = l_Lean_MessageData_ofConstName(v_declName_3722_, v___x_3777_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3782_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3783_;
}
v___jp_3733_:
{
lean_object* v___x_3736_; lean_object* v_env_3737_; lean_object* v_nextMacroScope_3738_; lean_object* v_ngen_3739_; lean_object* v_auxDeclNGen_3740_; lean_object* v_traceState_3741_; lean_object* v_messages_3742_; lean_object* v_infoState_3743_; lean_object* v_snapshotTasks_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3774_; 
v___x_3736_ = lean_st_ref_take(v___y_3735_);
v_env_3737_ = lean_ctor_get(v___x_3736_, 0);
v_nextMacroScope_3738_ = lean_ctor_get(v___x_3736_, 1);
v_ngen_3739_ = lean_ctor_get(v___x_3736_, 2);
v_auxDeclNGen_3740_ = lean_ctor_get(v___x_3736_, 3);
v_traceState_3741_ = lean_ctor_get(v___x_3736_, 4);
v_messages_3742_ = lean_ctor_get(v___x_3736_, 6);
v_infoState_3743_ = lean_ctor_get(v___x_3736_, 7);
v_snapshotTasks_3744_ = lean_ctor_get(v___x_3736_, 8);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v___x_3736_, 5);
lean_dec(v_unused_3775_);
v___x_3746_ = v___x_3736_;
v_isShared_3747_ = v_isSharedCheck_3774_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_snapshotTasks_3744_);
lean_inc(v_infoState_3743_);
lean_inc(v_messages_3742_);
lean_inc(v_traceState_3741_);
lean_inc(v_auxDeclNGen_3740_);
lean_inc(v_ngen_3739_);
lean_inc(v_nextMacroScope_3738_);
lean_inc(v_env_3737_);
lean_dec(v___x_3736_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3774_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3754_; 
v___x_3748_ = l_Lean_docStringExt;
v___x_3749_ = lean_box(2);
v___x_3750_ = lean_box(0);
v___x_3751_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3748_, v_env_3737_, v___f_3732_, v___x_3749_, v___x_3750_);
v___x_3752_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3747_ == 0)
{
lean_ctor_set(v___x_3746_, 5, v___x_3752_);
lean_ctor_set(v___x_3746_, 0, v___x_3751_);
v___x_3754_ = v___x_3746_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_nextMacroScope_3738_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_ngen_3739_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_auxDeclNGen_3740_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_traceState_3741_);
lean_ctor_set(v_reuseFailAlloc_3773_, 5, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3773_, 6, v_messages_3742_);
lean_ctor_set(v_reuseFailAlloc_3773_, 7, v_infoState_3743_);
lean_ctor_set(v_reuseFailAlloc_3773_, 8, v_snapshotTasks_3744_);
v___x_3754_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_mctx_3757_; lean_object* v_zetaDeltaFVarIds_3758_; lean_object* v_postponed_3759_; lean_object* v_diag_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3771_; 
v___x_3755_ = lean_st_ref_set(v___y_3735_, v___x_3754_);
v___x_3756_ = lean_st_ref_take(v___y_3734_);
v_mctx_3757_ = lean_ctor_get(v___x_3756_, 0);
v_zetaDeltaFVarIds_3758_ = lean_ctor_get(v___x_3756_, 2);
v_postponed_3759_ = lean_ctor_get(v___x_3756_, 3);
v_diag_3760_ = lean_ctor_get(v___x_3756_, 4);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; 
v_unused_3772_ = lean_ctor_get(v___x_3756_, 1);
lean_dec(v_unused_3772_);
v___x_3762_ = v___x_3756_;
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_diag_3760_);
lean_inc(v_postponed_3759_);
lean_inc(v_zetaDeltaFVarIds_3758_);
lean_inc(v_mctx_3757_);
lean_dec(v___x_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3771_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3764_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 1, v___x_3764_);
v___x_3766_ = v___x_3762_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_mctx_3757_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_zetaDeltaFVarIds_3758_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_postponed_3759_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_diag_3760_);
v___x_3766_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3767_ = lean_st_ref_set(v___y_3734_, v___x_3766_);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3768_);
return v___x_3769_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
return v_res_3792_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
return v___x_3795_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
return v___x_3798_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
return v___x_3801_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3804_ = l_Lean_stringToMessageData(v___x_3803_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v_env_3814_; uint8_t v___x_3815_; lean_object* v___x_3816_; 
v___x_3813_ = lean_st_ref_get(v_a_3811_);
v_env_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc_ref(v_env_3814_);
lean_dec(v___x_3813_);
v___x_3815_ = 1;
lean_inc(v_declName_3805_);
v___x_3816_ = l_Lean_findInternalDocString_x3f(v_env_3814_, v_declName_3805_, v___x_3815_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref(v___x_3816_);
if (lean_obj_tag(v_a_3817_) == 1)
{
lean_object* v_val_3818_; 
v_val_3818_ = lean_ctor_get(v_a_3817_, 0);
lean_inc(v_val_3818_);
lean_dec_ref(v_a_3817_);
if (lean_obj_tag(v_val_3818_) == 0)
{
lean_object* v_val_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3841_; 
v_val_3819_ = lean_ctor_get(v_val_3818_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v_val_3818_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3821_ = v_val_3818_;
v_isShared_3822_ = v_isSharedCheck_3841_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_val_3819_);
lean_dec(v_val_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3841_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_removeBuiltinDocString(v_declName_3805_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; 
lean_dec_ref(v___x_3823_);
lean_del_object(v___x_3821_);
lean_inc(v_declName_3805_);
v___x_3824_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref(v___x_3824_);
v___x_3825_ = l_Lean_addVersoDocStringFromString(v_declName_3805_, v_val_3819_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3825_;
}
else
{
lean_dec(v_val_3819_);
lean_dec(v_declName_3805_);
return v___x_3824_;
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v_val_3819_);
lean_dec(v_declName_3805_);
v_a_3826_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3828_ = v___x_3823_;
v_isShared_3829_ = v_isSharedCheck_3840_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3823_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3840_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v_ref_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v_ref_3830_ = lean_ctor_get(v_a_3810_, 5);
v___x_3831_ = lean_io_error_to_string(v_a_3826_);
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 3);
lean_ctor_set(v___x_3821_, 0, v___x_3831_);
v___x_3833_ = v___x_3821_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3834_ = l_Lean_MessageData_ofFormat(v___x_3833_);
lean_inc(v_ref_3830_);
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v_ref_3830_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 0, v___x_3835_);
v___x_3837_ = v___x_3828_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
}
else
{
lean_object* v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_dec(v_val_3818_);
v___x_3842_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3843_ = 0;
v___x_3844_ = l_Lean_MessageData_ofConstName(v_declName_3805_, v___x_3843_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3842_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3847_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3848_;
}
}
else
{
lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_a_3817_);
v___x_3849_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3850_ = 0;
v___x_3851_ = l_Lean_MessageData_ofConstName(v_declName_3805_, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3854_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3855_;
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_declName_3805_);
v_a_3856_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3858_ = v___x_3816_;
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3816_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v_ref_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3866_; 
v_ref_3860_ = lean_ctor_get(v_a_3810_, 5);
v___x_3861_ = lean_io_error_to_string(v_a_3856_);
v___x_3862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
v___x_3863_ = l_Lean_MessageData_ofFormat(v___x_3862_);
lean_inc(v_ref_3860_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v_ref_3860_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3864_);
v___x_3866_ = v___x_3858_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_makeDocStringVerso(v_declName_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3878_, lean_object* v_k_3879_, lean_object* v_t_3880_, lean_object* v_h_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3879_, v_t_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3883_, lean_object* v_k_3884_, lean_object* v_t_3885_, lean_object* v_h_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3883_, v_k_3884_, v_t_3885_, v_h_3886_);
lean_dec(v_k_3884_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3888_, lean_object* v_binders_3889_, lean_object* v_docComment_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_options_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; 
v_options_3898_ = lean_ctor_get(v_a_3895_, 2);
v___x_3899_ = l_Lean_doc_verso;
v___x_3900_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_3898_, v___x_3899_);
v___x_3901_ = l_Lean_addDocStringOf(v___x_3900_, v_declName_3888_, v_binders_3889_, v_docComment_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3902_, lean_object* v_binders_3903_, lean_object* v_docComment_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_addDocString(v_declName_3902_, v_binders_3903_, v_docComment_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3913_, lean_object* v_binders_3914_, lean_object* v_docString_x3f_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3915_) == 0)
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
lean_dec(v_binders_3914_);
lean_dec(v_declName_3913_);
v___x_3923_ = lean_box(0);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
return v___x_3924_;
}
else
{
lean_object* v_val_3925_; lean_object* v___x_3926_; 
v_val_3925_ = lean_ctor_get(v_docString_x3f_3915_, 0);
lean_inc(v_val_3925_);
lean_dec_ref(v_docString_x3f_3915_);
v___x_3926_ = l_Lean_addDocString(v_declName_3913_, v_binders_3914_, v_val_3925_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3927_, lean_object* v_binders_3928_, lean_object* v_docString_x3f_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_addDocString_x27(v_declName_3927_, v_binders_3928_, v_docString_x3f_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; lean_object* v_nextMacroScope_3943_; lean_object* v_ngen_3944_; lean_object* v_auxDeclNGen_3945_; lean_object* v_traceState_3946_; lean_object* v_messages_3947_; lean_object* v_infoState_3948_; lean_object* v_snapshotTasks_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3975_; 
v___x_3942_ = lean_st_ref_take(v___y_3940_);
v_nextMacroScope_3943_ = lean_ctor_get(v___x_3942_, 1);
v_ngen_3944_ = lean_ctor_get(v___x_3942_, 2);
v_auxDeclNGen_3945_ = lean_ctor_get(v___x_3942_, 3);
v_traceState_3946_ = lean_ctor_get(v___x_3942_, 4);
v_messages_3947_ = lean_ctor_get(v___x_3942_, 6);
v_infoState_3948_ = lean_ctor_get(v___x_3942_, 7);
v_snapshotTasks_3949_ = lean_ctor_get(v___x_3942_, 8);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; lean_object* v_unused_3977_; 
v_unused_3976_ = lean_ctor_get(v___x_3942_, 5);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v___x_3942_, 0);
lean_dec(v_unused_3977_);
v___x_3951_ = v___x_3942_;
v_isShared_3952_ = v_isSharedCheck_3975_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_snapshotTasks_3949_);
lean_inc(v_infoState_3948_);
lean_inc(v_messages_3947_);
lean_inc(v_traceState_3946_);
lean_inc(v_auxDeclNGen_3945_);
lean_inc(v_ngen_3944_);
lean_inc(v_nextMacroScope_3943_);
lean_dec(v___x_3942_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3975_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 5, v___x_3953_);
lean_ctor_set(v___x_3951_, 0, v_env_3938_);
v___x_3955_ = v___x_3951_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_env_3938_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_nextMacroScope_3943_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_ngen_3944_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_auxDeclNGen_3945_);
lean_ctor_set(v_reuseFailAlloc_3974_, 4, v_traceState_3946_);
lean_ctor_set(v_reuseFailAlloc_3974_, 5, v___x_3953_);
lean_ctor_set(v_reuseFailAlloc_3974_, 6, v_messages_3947_);
lean_ctor_set(v_reuseFailAlloc_3974_, 7, v_infoState_3948_);
lean_ctor_set(v_reuseFailAlloc_3974_, 8, v_snapshotTasks_3949_);
v___x_3955_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v_mctx_3958_; lean_object* v_zetaDeltaFVarIds_3959_; lean_object* v_postponed_3960_; lean_object* v_diag_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3972_; 
v___x_3956_ = lean_st_ref_set(v___y_3940_, v___x_3955_);
v___x_3957_ = lean_st_ref_take(v___y_3939_);
v_mctx_3958_ = lean_ctor_get(v___x_3957_, 0);
v_zetaDeltaFVarIds_3959_ = lean_ctor_get(v___x_3957_, 2);
v_postponed_3960_ = lean_ctor_get(v___x_3957_, 3);
v_diag_3961_ = lean_ctor_get(v___x_3957_, 4);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; 
v_unused_3973_ = lean_ctor_get(v___x_3957_, 1);
lean_dec(v_unused_3973_);
v___x_3963_ = v___x_3957_;
v_isShared_3964_ = v_isSharedCheck_3972_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_diag_3961_);
lean_inc(v_postponed_3960_);
lean_inc(v_zetaDeltaFVarIds_3959_);
lean_inc(v_mctx_3958_);
lean_dec(v___x_3957_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3972_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3965_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 1, v___x_3965_);
v___x_3967_ = v___x_3963_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_mctx_3958_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_zetaDeltaFVarIds_3959_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_postponed_3960_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v_diag_3961_);
v___x_3967_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_st_ref_set(v___y_3939_, v___x_3967_);
v___x_3969_ = lean_box(0);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3978_, v___y_3979_, v___y_3980_);
lean_dec(v___y_3980_);
lean_dec(v___y_3979_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v_env_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3991_ = lean_st_ref_get(v___y_3989_);
v_env_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_ref(v_env_3992_);
lean_dec(v___x_3991_);
v___x_3993_ = l_Lean_getMainModuleDoc(v_env_3992_);
v___x_3994_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3993_);
lean_dec_ref(v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec_ref(v_docs_3983_);
v___x_3995_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_3996_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3995_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_3996_;
}
else
{
lean_object* v___x_3997_; lean_object* v_env_3998_; lean_object* v___x_3999_; 
v___x_3997_ = lean_st_ref_get(v___y_3989_);
v_env_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc_ref(v_env_3998_);
lean_dec(v___x_3997_);
v___x_3999_ = l_Lean_addVersoModuleDocSnippet(v_env_3998_, v_docs_3983_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
v___x_4001_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_4002_ = l_Lean_stringToMessageData(v_a_4000_);
v___x_4003_ = l_Lean_indentD(v___x_4002_);
v___x_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4001_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4004_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_4005_;
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4007_; 
v_a_4006_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_3999_);
v___x_4007_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4006_, v___y_3987_, v___y_3989_);
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4017_, lean_object* v_docComment_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v___x_4026_; 
v___x_4026_ = l_Lean_versoModDocString(v_range_4017_, v_docComment_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4026_);
v___x_4028_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_a_4027_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_a_4029_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4026_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4026_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4037_, lean_object* v_docComment_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_addVersoModDocString(v_range_4037_, v_docComment_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
lean_dec(v_docComment_4038_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4047_, v___y_4051_, v___y_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4064_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term_TermElabM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Add(builtin);
}
#ifdef __cplusplus
}
#endif
