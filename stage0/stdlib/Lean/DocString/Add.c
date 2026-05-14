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
uint8_t v___x_10580__boxed_884_; uint8_t v_suppressElabErrors_boxed_885_; uint8_t v_res_886_; lean_object* v_r_887_; 
v___x_10580__boxed_884_ = lean_unbox(v___x_881_);
v_suppressElabErrors_boxed_885_ = lean_unbox(v_suppressElabErrors_882_);
v_res_886_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_10580__boxed_884_, v_suppressElabErrors_boxed_885_, v_x_883_);
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
uint8_t v___x_10652__boxed_919_; uint8_t v_suppressElabErrors_boxed_920_; uint8_t v_res_921_; lean_object* v_r_922_; 
v___x_10652__boxed_919_ = lean_unbox(v___x_916_);
v_suppressElabErrors_boxed_920_ = lean_unbox(v_suppressElabErrors_917_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10652__boxed_919_, v_suppressElabErrors_boxed_920_, v_x_918_);
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
lean_object* v_a_939_; lean_object* v_snd_940_; lean_object* v_fst_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_999_; 
v_a_939_ = lean_array_uget(v_as_925_, v_i_927_);
v_snd_940_ = lean_ctor_get(v_a_939_, 1);
v_fst_941_ = lean_ctor_get(v_a_939_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_a_939_);
if (v_isSharedCheck_999_ == 0)
{
v___x_943_ = v_a_939_;
v_isShared_944_ = v_isSharedCheck_999_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_snd_940_);
lean_inc(v_fst_941_);
lean_dec(v_a_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_999_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_997_; 
v_snd_945_ = lean_ctor_get(v_snd_940_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_snd_940_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_snd_940_, 0);
lean_dec(v_unused_998_);
v___x_947_ = v_snd_940_;
v_isShared_948_ = v_isSharedCheck_997_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_dec(v_snd_940_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_997_;
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
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___f_995_; uint8_t v___x_996_; 
v___x_993_ = lean_box(v___x_953_);
v___x_994_ = lean_box(v_suppressElabErrors_950_);
v___f_995_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_995_, 0, v___x_993_);
lean_closure_set(v___f_995_, 1, v___x_994_);
lean_inc_ref(v___x_960_);
v___x_996_ = l_Lean_MessageData_hasTag(v___f_995_, v___x_960_);
if (v___x_996_ == 0)
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
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_currNamespace_965_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_openDecls_966_);
v___x_968_ = v_reuseFailAlloc_992_;
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
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_960_);
v___x_970_ = v_reuseFailAlloc_991_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_cache_977_; lean_object* v_messages_978_; lean_object* v_infoState_979_; lean_object* v_snapshotTasks_980_; lean_object* v_newDecls_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
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
v_newDecls_981_ = lean_ctor_get(v___x_964_, 9);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v___x_964_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_newDecls_981_);
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
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = l_Lean_MessageLog_add(v___x_971_, v_messages_978_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 6, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_env_972_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_nextMacroScope_973_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_ngen_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_auxDeclNGen_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_traceState_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_cache_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 6, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_989_, 7, v_infoState_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 8, v_snapshotTasks_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 9, v_newDecls_981_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_st_ref_set(v___y_963_, v___x_987_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v_as_1002_, lean_object* v_sz_1003_, lean_object* v_i_1004_, lean_object* v_b_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
size_t v_sz_boxed_1009_; size_t v_i_boxed_1010_; lean_object* v_res_1011_; 
v_sz_boxed_1009_ = lean_unbox_usize(v_sz_1003_);
lean_dec(v_sz_1003_);
v_i_boxed_1010_ = lean_unbox_usize(v_i_1004_);
lean_dec(v_i_1004_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1000_, v___x_1001_, v_as_1002_, v_sz_boxed_1009_, v_i_boxed_1010_, v_b_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec_ref(v_as_1002_);
lean_dec(v___x_1001_);
return v_res_1011_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_box(1);
v___x_1013_ = l_Lean_MessageData_ofFormat(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2));
v___x_1018_ = l_Lean_MessageData_ofFormat(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
return v_x_1019_;
}
else
{
lean_object* v_head_1021_; lean_object* v_tail_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1044_; 
v_head_1021_ = lean_ctor_get(v_x_1020_, 0);
v_tail_1022_ = lean_ctor_get(v_x_1020_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_x_1020_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1024_ = v_x_1020_;
v_isShared_1025_ = v_isSharedCheck_1044_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_tail_1022_);
lean_inc(v_head_1021_);
lean_dec(v_x_1020_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1044_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_before_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1042_; 
v_before_1026_ = lean_ctor_get(v_head_1021_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_head_1021_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_head_1021_, 1);
lean_dec(v_unused_1043_);
v___x_1028_ = v_head_1021_;
v_isShared_1029_ = v_isSharedCheck_1042_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_before_1026_);
lean_dec(v_head_1021_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1042_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 7);
lean_ctor_set(v___x_1028_, 1, v___x_1030_);
lean_ctor_set(v___x_1028_, 0, v_x_1019_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_x_1019_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
v___x_1033_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 7);
lean_ctor_set(v___x_1024_, 1, v___x_1033_);
lean_ctor_set(v___x_1024_, 0, v___x_1032_);
v___x_1035_ = v___x_1024_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = l_Lean_MessageData_ofSyntax(v_before_1026_);
v___x_1037_ = l_Lean_indentD(v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1035_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v_x_1019_ = v___x_1038_;
v_x_1020_ = v_tail_1022_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object* v_opts_1045_, lean_object* v_opt_1046_){
_start:
{
lean_object* v_name_1047_; lean_object* v_defValue_1048_; lean_object* v_map_1049_; lean_object* v___x_1050_; 
v_name_1047_ = lean_ctor_get(v_opt_1046_, 0);
v_defValue_1048_ = lean_ctor_get(v_opt_1046_, 1);
v_map_1049_ = lean_ctor_get(v_opts_1045_, 0);
v___x_1050_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1049_, v_name_1047_);
if (lean_obj_tag(v___x_1050_) == 0)
{
uint8_t v___x_1051_; 
v___x_1051_ = lean_unbox(v_defValue_1048_);
return v___x_1051_;
}
else
{
lean_object* v_val_1052_; 
v_val_1052_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1052_);
lean_dec_ref(v___x_1050_);
if (lean_obj_tag(v_val_1052_) == 1)
{
uint8_t v_v_1053_; 
v_v_1053_ = lean_ctor_get_uint8(v_val_1052_, 0);
lean_dec_ref(v_val_1052_);
return v_v_1053_;
}
else
{
uint8_t v___x_1054_; 
lean_dec(v_val_1052_);
v___x_1054_ = lean_unbox(v_defValue_1048_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_opts_1055_, lean_object* v_opt_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_opts_1055_, v_opt_1056_);
lean_dec_ref(v_opt_1056_);
lean_dec_ref(v_opts_1055_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1));
v___x_1063_ = l_Lean_MessageData_ofFormat(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_1064_, lean_object* v_macroStack_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_options_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v_options_1068_ = lean_ctor_get(v___y_1066_, 2);
v___x_1069_ = l_Lean_Elab_pp_macroStack;
v___x_1070_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1068_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_macroStack_1065_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_msgData_1064_);
return v___x_1071_;
}
else
{
if (lean_obj_tag(v_macroStack_1065_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v_msgData_1064_);
return v___x_1072_;
}
else
{
lean_object* v_head_1073_; lean_object* v_after_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1089_; 
v_head_1073_ = lean_ctor_get(v_macroStack_1065_, 0);
lean_inc(v_head_1073_);
v_after_1074_ = lean_ctor_get(v_head_1073_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_head_1073_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_head_1073_, 0);
lean_dec(v_unused_1090_);
v___x_1076_ = v_head_1073_;
v_isShared_1077_ = v_isSharedCheck_1089_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_after_1074_);
lean_dec(v_head_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1089_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1077_ == 0)
{
lean_ctor_set_tag(v___x_1076_, 7);
lean_ctor_set(v___x_1076_, 1, v___x_1078_);
lean_ctor_set(v___x_1076_, 0, v_msgData_1064_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_msgData_1064_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_msgData_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1081_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_ofSyntax(v_after_1074_);
v___x_1084_ = l_Lean_indentD(v___x_1083_);
v_msgData_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1085_, 0, v___x_1082_);
lean_ctor_set(v_msgData_1085_, 1, v___x_1084_);
v___x_1086_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(v_msgData_1085_, v_macroStack_1065_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1091_, lean_object* v_macroStack_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1091_, v_macroStack_1092_, v___y_1093_);
lean_dec_ref(v___y_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_env_1103_; lean_object* v___x_1104_; lean_object* v_mctx_1105_; lean_object* v_lctx_1106_; lean_object* v_options_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1102_ = lean_st_ref_get(v___y_1100_);
v_env_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_ref(v_env_1103_);
lean_dec(v___x_1102_);
v___x_1104_ = lean_st_ref_get(v___y_1098_);
v_mctx_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc_ref(v_mctx_1105_);
lean_dec(v___x_1104_);
v_lctx_1106_ = lean_ctor_get(v___y_1097_, 2);
v_options_1107_ = lean_ctor_get(v___y_1099_, 2);
lean_inc_ref(v_options_1107_);
lean_inc_ref(v_lctx_1106_);
v___x_1108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1108_, 0, v_env_1103_);
lean_ctor_set(v___x_1108_, 1, v_mctx_1105_);
lean_ctor_set(v___x_1108_, 2, v_lctx_1106_);
lean_ctor_set(v___x_1108_, 3, v_options_1107_);
v___x_1109_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_msgData_1096_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_ref_1126_; lean_object* v___x_1127_; lean_object* v_a_1128_; lean_object* v_macroStack_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v_ref_1126_ = lean_ctor_get(v___y_1123_, 5);
v___x_1127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msg_1118_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref(v___x_1127_);
v_macroStack_1129_ = lean_ctor_get(v___y_1119_, 1);
v___x_1130_ = l_Lean_Elab_getBetterRef(v_ref_1126_, v_macroStack_1129_);
lean_inc(v_macroStack_1129_);
v___x_1131_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_a_1128_, v_macroStack_1129_, v___y_1123_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1130_);
lean_ctor_set(v___x_1136_, 1, v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 1);
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1150_, lean_object* v_msg_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_fileName_1159_; lean_object* v_fileMap_1160_; lean_object* v_options_1161_; lean_object* v_currRecDepth_1162_; lean_object* v_maxRecDepth_1163_; lean_object* v_ref_1164_; lean_object* v_currNamespace_1165_; lean_object* v_openDecls_1166_; lean_object* v_initHeartbeats_1167_; lean_object* v_maxHeartbeats_1168_; lean_object* v_quotContext_1169_; lean_object* v_currMacroScope_1170_; uint8_t v_diag_1171_; lean_object* v_cancelTk_x3f_1172_; uint8_t v_suppressElabErrors_1173_; lean_object* v_inheritedTraceOptions_1174_; lean_object* v_ref_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_fileName_1159_ = lean_ctor_get(v___y_1156_, 0);
v_fileMap_1160_ = lean_ctor_get(v___y_1156_, 1);
v_options_1161_ = lean_ctor_get(v___y_1156_, 2);
v_currRecDepth_1162_ = lean_ctor_get(v___y_1156_, 3);
v_maxRecDepth_1163_ = lean_ctor_get(v___y_1156_, 4);
v_ref_1164_ = lean_ctor_get(v___y_1156_, 5);
v_currNamespace_1165_ = lean_ctor_get(v___y_1156_, 6);
v_openDecls_1166_ = lean_ctor_get(v___y_1156_, 7);
v_initHeartbeats_1167_ = lean_ctor_get(v___y_1156_, 8);
v_maxHeartbeats_1168_ = lean_ctor_get(v___y_1156_, 9);
v_quotContext_1169_ = lean_ctor_get(v___y_1156_, 10);
v_currMacroScope_1170_ = lean_ctor_get(v___y_1156_, 11);
v_diag_1171_ = lean_ctor_get_uint8(v___y_1156_, sizeof(void*)*14);
v_cancelTk_x3f_1172_ = lean_ctor_get(v___y_1156_, 12);
v_suppressElabErrors_1173_ = lean_ctor_get_uint8(v___y_1156_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1174_ = lean_ctor_get(v___y_1156_, 13);
v_ref_1175_ = l_Lean_replaceRef(v_ref_1150_, v_ref_1164_);
lean_inc_ref(v_inheritedTraceOptions_1174_);
lean_inc(v_cancelTk_x3f_1172_);
lean_inc(v_currMacroScope_1170_);
lean_inc(v_quotContext_1169_);
lean_inc(v_maxHeartbeats_1168_);
lean_inc(v_initHeartbeats_1167_);
lean_inc(v_openDecls_1166_);
lean_inc(v_currNamespace_1165_);
lean_inc(v_maxRecDepth_1163_);
lean_inc(v_currRecDepth_1162_);
lean_inc_ref(v_options_1161_);
lean_inc_ref(v_fileMap_1160_);
lean_inc_ref(v_fileName_1159_);
v___x_1176_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1176_, 0, v_fileName_1159_);
lean_ctor_set(v___x_1176_, 1, v_fileMap_1160_);
lean_ctor_set(v___x_1176_, 2, v_options_1161_);
lean_ctor_set(v___x_1176_, 3, v_currRecDepth_1162_);
lean_ctor_set(v___x_1176_, 4, v_maxRecDepth_1163_);
lean_ctor_set(v___x_1176_, 5, v_ref_1175_);
lean_ctor_set(v___x_1176_, 6, v_currNamespace_1165_);
lean_ctor_set(v___x_1176_, 7, v_openDecls_1166_);
lean_ctor_set(v___x_1176_, 8, v_initHeartbeats_1167_);
lean_ctor_set(v___x_1176_, 9, v_maxHeartbeats_1168_);
lean_ctor_set(v___x_1176_, 10, v_quotContext_1169_);
lean_ctor_set(v___x_1176_, 11, v_currMacroScope_1170_);
lean_ctor_set(v___x_1176_, 12, v_cancelTk_x3f_1172_);
lean_ctor_set(v___x_1176_, 13, v_inheritedTraceOptions_1174_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*14, v_diag_1171_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*14 + 1, v_suppressElabErrors_1173_);
v___x_1177_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___x_1176_, v___y_1157_);
lean_dec_ref(v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1178_, lean_object* v_msg_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1178_, v_msg_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v_ref_1178_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; uint8_t v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; uint8_t v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1312_; uint8_t v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
lean_inc(v_docComment_1188_);
v___x_1362_ = l_Lean_Syntax_getKind(v_docComment_1188_);
v___x_1363_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_1364_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_1365_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_1366_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_1367_ = lean_name_eq(v___x_1362_, v___x_1366_);
lean_dec(v___x_1362_);
if (v___x_1367_ == 0)
{
goto v___jp_1339_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = l_Lean_Syntax_getArg(v_docComment_1188_, v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v_kind_1370_; 
v_kind_1370_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_kind_1370_);
if (lean_obj_tag(v_kind_1370_) == 1)
{
lean_object* v_pre_1371_; 
v_pre_1371_ = lean_ctor_get(v_kind_1370_, 0);
lean_inc(v_pre_1371_);
if (lean_obj_tag(v_pre_1371_) == 1)
{
lean_object* v_pre_1372_; 
v_pre_1372_ = lean_ctor_get(v_pre_1371_, 0);
lean_inc(v_pre_1372_);
if (lean_obj_tag(v_pre_1372_) == 1)
{
lean_object* v_pre_1373_; 
v_pre_1373_ = lean_ctor_get(v_pre_1372_, 0);
lean_inc(v_pre_1373_);
if (lean_obj_tag(v_pre_1373_) == 1)
{
lean_object* v_pre_1374_; 
v_pre_1374_ = lean_ctor_get(v_pre_1373_, 0);
lean_inc(v_pre_1374_);
if (lean_obj_tag(v_pre_1374_) == 0)
{
lean_object* v_info_1375_; lean_object* v_args_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1402_; 
v_info_1375_ = lean_ctor_get(v___x_1369_, 0);
v_args_1376_ = lean_ctor_get(v___x_1369_, 2);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1369_, 1);
lean_dec(v_unused_1403_);
v___x_1378_ = v___x_1369_;
v_isShared_1379_ = v_isSharedCheck_1402_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_args_1376_);
lean_inc(v_info_1375_);
lean_dec(v___x_1369_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1402_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_str_1380_; lean_object* v_str_1381_; lean_object* v_str_1382_; lean_object* v_str_1383_; uint8_t v___x_1384_; 
v_str_1380_ = lean_ctor_get(v_kind_1370_, 1);
lean_inc_ref(v_str_1380_);
lean_dec_ref(v_kind_1370_);
v_str_1381_ = lean_ctor_get(v_pre_1371_, 1);
lean_inc_ref(v_str_1381_);
lean_dec_ref(v_pre_1371_);
v_str_1382_ = lean_ctor_get(v_pre_1372_, 1);
lean_inc_ref(v_str_1382_);
lean_dec_ref(v_pre_1372_);
v_str_1383_ = lean_ctor_get(v_pre_1373_, 1);
lean_inc_ref(v_str_1383_);
lean_dec_ref(v_pre_1373_);
v___x_1384_ = lean_string_dec_eq(v_str_1383_, v___x_1363_);
lean_dec_ref(v_str_1383_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v_str_1382_);
lean_dec_ref(v_str_1381_);
lean_dec_ref(v_str_1380_);
lean_del_object(v___x_1378_);
lean_dec_ref(v_args_1376_);
lean_dec(v_info_1375_);
goto v___jp_1339_;
}
else
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_string_dec_eq(v_str_1382_, v___x_1364_);
lean_dec_ref(v_str_1382_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_str_1381_);
lean_dec_ref(v_str_1380_);
lean_del_object(v___x_1378_);
lean_dec_ref(v_args_1376_);
lean_dec(v_info_1375_);
goto v___jp_1339_;
}
else
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_string_dec_eq(v_str_1381_, v___x_1365_);
lean_dec_ref(v_str_1381_);
if (v___x_1386_ == 0)
{
lean_dec_ref(v_str_1380_);
lean_del_object(v___x_1378_);
lean_dec_ref(v_args_1376_);
lean_dec(v_info_1375_);
goto v___jp_1339_;
}
else
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_1388_ = lean_string_dec_eq(v_str_1380_, v___x_1387_);
lean_dec_ref(v_str_1380_);
if (v___x_1388_ == 0)
{
lean_del_object(v___x_1378_);
lean_dec_ref(v_args_1376_);
lean_dec(v_info_1375_);
goto v___jp_1339_;
}
else
{
lean_dec(v_docComment_1188_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_del_object(v___x_1378_);
lean_dec_ref(v_args_1376_);
lean_dec(v_info_1375_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1391_ = l_Lean_Name_str___override(v_pre_1374_, v___x_1363_);
v___x_1392_ = l_Lean_Name_str___override(v___x_1391_, v___x_1364_);
v___x_1393_ = l_Lean_Name_str___override(v___x_1392_, v___x_1365_);
v___x_1394_ = l_Lean_Name_str___override(v___x_1393_, v___x_1387_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 1, v___x_1394_);
v___x_1396_ = v___x_1378_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_info_1375_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_args_1376_);
v___x_1396_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = l_Lean_Syntax_getArg(v___x_1396_, v___x_1397_);
lean_dec_ref(v___x_1396_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
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
lean_dec_ref(v_pre_1373_);
lean_dec(v_pre_1374_);
lean_dec_ref(v_pre_1372_);
lean_dec_ref(v_pre_1371_);
lean_dec_ref(v_kind_1370_);
lean_dec_ref(v___x_1369_);
goto v___jp_1339_;
}
}
else
{
lean_dec(v_pre_1373_);
lean_dec_ref(v_pre_1372_);
lean_dec_ref(v_pre_1371_);
lean_dec_ref(v_kind_1370_);
lean_dec_ref(v___x_1369_);
goto v___jp_1339_;
}
}
else
{
lean_dec_ref(v_pre_1371_);
lean_dec(v_pre_1372_);
lean_dec_ref(v_kind_1370_);
lean_dec_ref(v___x_1369_);
goto v___jp_1339_;
}
}
else
{
lean_dec_ref(v_kind_1370_);
lean_dec(v_pre_1371_);
lean_dec_ref(v___x_1369_);
goto v___jp_1339_;
}
}
else
{
lean_dec(v_kind_1370_);
lean_dec_ref(v___x_1369_);
goto v___jp_1339_;
}
}
else
{
lean_dec(v___x_1369_);
goto v___jp_1339_;
}
}
v___jp_1196_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
v___jp_1199_:
{
lean_object* v___x_1209_; lean_object* v_currNamespace_1210_; lean_object* v_openDecls_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_env_1215_; lean_object* v_nextMacroScope_1216_; lean_object* v_ngen_1217_; lean_object* v_auxDeclNGen_1218_; lean_object* v_traceState_1219_; lean_object* v_cache_1220_; lean_object* v_messages_1221_; lean_object* v_infoState_1222_; lean_object* v_snapshotTasks_1223_; lean_object* v_newDecls_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1233_; 
v___x_1209_ = lean_st_ref_take(v___y_1208_);
v_currNamespace_1210_ = lean_ctor_get(v___y_1207_, 6);
v_openDecls_1211_ = lean_ctor_get(v___y_1207_, 7);
lean_inc(v_openDecls_1211_);
lean_inc(v_currNamespace_1210_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_currNamespace_1210_);
lean_ctor_set(v___x_1212_, 1, v_openDecls_1211_);
v___x_1213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___y_1206_);
lean_inc(v___y_1201_);
lean_inc_ref(v___y_1205_);
v___x_1214_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1214_, 0, v___y_1205_);
lean_ctor_set(v___x_1214_, 1, v___y_1203_);
lean_ctor_set(v___x_1214_, 2, v___y_1201_);
lean_ctor_set(v___x_1214_, 3, v___y_1202_);
lean_ctor_set(v___x_1214_, 4, v___x_1213_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5, v___y_1200_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5 + 1, v___y_1204_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5 + 2, v___y_1200_);
v_env_1215_ = lean_ctor_get(v___x_1209_, 0);
v_nextMacroScope_1216_ = lean_ctor_get(v___x_1209_, 1);
v_ngen_1217_ = lean_ctor_get(v___x_1209_, 2);
v_auxDeclNGen_1218_ = lean_ctor_get(v___x_1209_, 3);
v_traceState_1219_ = lean_ctor_get(v___x_1209_, 4);
v_cache_1220_ = lean_ctor_get(v___x_1209_, 5);
v_messages_1221_ = lean_ctor_get(v___x_1209_, 6);
v_infoState_1222_ = lean_ctor_get(v___x_1209_, 7);
v_snapshotTasks_1223_ = lean_ctor_get(v___x_1209_, 8);
v_newDecls_1224_ = lean_ctor_get(v___x_1209_, 9);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1226_ = v___x_1209_;
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_newDecls_1224_);
lean_inc(v_snapshotTasks_1223_);
lean_inc(v_infoState_1222_);
lean_inc(v_messages_1221_);
lean_inc(v_cache_1220_);
lean_inc(v_traceState_1219_);
lean_inc(v_auxDeclNGen_1218_);
lean_inc(v_ngen_1217_);
lean_inc(v_nextMacroScope_1216_);
lean_inc(v_env_1215_);
lean_dec(v___x_1209_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1233_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = l_Lean_MessageLog_add(v___x_1214_, v_messages_1221_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 6, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_env_1215_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_nextMacroScope_1216_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_ngen_1217_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_auxDeclNGen_1218_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_traceState_1219_);
lean_ctor_set(v_reuseFailAlloc_1232_, 5, v_cache_1220_);
lean_ctor_set(v_reuseFailAlloc_1232_, 6, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1232_, 7, v_infoState_1222_);
lean_ctor_set(v_reuseFailAlloc_1232_, 8, v_snapshotTasks_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 9, v_newDecls_1224_);
v___x_1230_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_st_ref_set(v___y_1208_, v___x_1230_);
goto v___jp_1196_;
}
}
}
v___jp_1234_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
lean_inc_ref(v___y_1241_);
v___x_1242_ = l_Lean_Parser_ParserState_allErrors(v___y_1241_);
v___x_1243_ = lean_array_get_size(v___x_1242_);
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_nat_dec_eq(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
lean_dec_ref(v___y_1241_);
lean_dec_ref(v___y_1239_);
v___x_1246_ = lean_box(0);
v_sz_1247_ = lean_array_size(v___x_1242_);
v___x_1248_ = ((size_t)0ULL);
lean_inc_ref(v___y_1237_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1237_, v___x_1243_, v___x_1242_, v_sz_1247_, v___x_1248_, v___x_1246_, v___y_1193_, v___y_1194_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1257_; 
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1249_, 0);
lean_dec(v_unused_1258_);
v___x_1251_ = v___x_1249_;
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v___x_1249_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1257_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_box(0);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1253_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1249_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1249_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
else
{
lean_object* v_stxStack_1267_; lean_object* v_pos_1268_; uint8_t v___x_1269_; 
lean_dec_ref(v___x_1242_);
v_stxStack_1267_ = lean_ctor_get(v___y_1241_, 0);
lean_inc_ref(v_stxStack_1267_);
v_pos_1268_ = lean_ctor_get(v___y_1241_, 2);
lean_inc(v_pos_1268_);
lean_dec_ref(v___y_1241_);
v___x_1269_ = l_Lean_Parser_InputContext_atEnd(v___y_1239_, v_pos_1268_);
lean_dec_ref(v___y_1239_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint32_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref(v_stxStack_1267_);
lean_inc_ref(v___y_1237_);
v___x_1270_ = l_Lean_FileMap_toPosition(v___y_1237_, v_pos_1268_);
v___x_1271_ = lean_box(0);
v___x_1272_ = 2;
v___x_1273_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1274_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1275_ = lean_string_utf8_get(v___y_1236_, v_pos_1268_);
lean_dec(v_pos_1268_);
v___x_1276_ = lean_string_push(v___x_1273_, v___x_1275_);
v___x_1277_ = lean_string_append(v___x_1274_, v___x_1276_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1279_ = lean_string_append(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
v___x_1281_ = l_Lean_MessageData_ofFormat(v___x_1280_);
if (v___y_1238_ == 0)
{
v___y_1200_ = v___x_1269_;
v___y_1201_ = v___x_1271_;
v___y_1202_ = v___x_1273_;
v___y_1203_ = v___x_1270_;
v___y_1204_ = v___x_1272_;
v___y_1205_ = v___y_1240_;
v___y_1206_ = v___x_1281_;
v___y_1207_ = v___y_1193_;
v___y_1208_ = v___y_1194_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___f_1284_; uint8_t v___x_1285_; 
v___x_1282_ = lean_box(v___x_1269_);
v___x_1283_ = lean_box(v___y_1235_);
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1284_, 0, v___x_1282_);
lean_closure_set(v___f_1284_, 1, v___x_1283_);
lean_inc_ref(v___x_1281_);
v___x_1285_ = l_Lean_MessageData_hasTag(v___f_1284_, v___x_1281_);
if (v___x_1285_ == 0)
{
lean_dec_ref(v___x_1281_);
lean_dec_ref(v___x_1270_);
goto v___jp_1196_;
}
else
{
v___y_1200_ = v___x_1269_;
v___y_1201_ = v___x_1271_;
v___y_1202_ = v___x_1273_;
v___y_1203_ = v___x_1270_;
v___y_1204_ = v___x_1272_;
v___y_1205_ = v___y_1240_;
v___y_1206_ = v___x_1281_;
v___y_1207_ = v___y_1193_;
v___y_1208_ = v___y_1194_;
goto v___jp_1199_;
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_pos_1268_);
v___x_1286_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1267_);
lean_dec_ref(v_stxStack_1267_);
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
v___jp_1289_:
{
if (v___y_1301_ == 0)
{
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v___y_1292_);
v___y_1235_ = v___y_1290_;
v___y_1236_ = v___y_1291_;
v___y_1237_ = v___y_1293_;
v___y_1238_ = v___y_1296_;
v___y_1239_ = v___y_1295_;
v___y_1240_ = v___y_1298_;
v___y_1241_ = v___y_1299_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_pos_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___y_1297_);
lean_ctor_set(v___x_1305_, 1, v___x_1302_);
v___x_1306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1302_);
lean_ctor_set(v___x_1306_, 1, v___x_1303_);
lean_ctor_set(v___x_1306_, 2, v___x_1304_);
lean_ctor_set(v___x_1306_, 3, v___x_1305_);
lean_ctor_set(v___x_1306_, 4, v___x_1302_);
v_pos_1307_ = lean_ctor_get(v___y_1299_, 2);
lean_inc(v_pos_1307_);
lean_dec_ref(v___y_1299_);
v___x_1308_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_1308_, 0, v___x_1306_);
v___x_1309_ = l_Lean_Parser_ParserState_setPos(v___y_1292_, v_pos_1307_);
lean_inc_ref(v___y_1295_);
v___x_1310_ = l_Lean_Parser_ParserFn_run(v___x_1308_, v___y_1295_, v___y_1300_, v___y_1294_, v___x_1309_);
v___y_1235_ = v___y_1290_;
v___y_1236_ = v___y_1291_;
v___y_1237_ = v___y_1293_;
v___y_1238_ = v___y_1296_;
v___y_1239_ = v___y_1295_;
v___y_1240_ = v___y_1298_;
v___y_1241_ = v___x_1310_;
goto v___jp_1234_;
}
}
v___jp_1311_:
{
lean_object* v___x_1323_; lean_object* v_env_1324_; lean_object* v_ictx_1325_; lean_object* v_pmctx_1326_; lean_object* v_blockCtxt_1327_; lean_object* v___x_1328_; lean_object* v_s_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_s_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1323_ = lean_st_ref_get(v___y_1194_);
v_env_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc_ref_n(v_env_1324_, 2);
lean_dec(v___x_1323_);
lean_inc(v___y_1322_);
lean_inc_ref_n(v___y_1314_, 2);
lean_inc_ref(v___y_1319_);
lean_inc_ref(v___y_1312_);
v_ictx_1325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1325_, 0, v___y_1312_);
lean_ctor_set(v_ictx_1325_, 1, v___y_1319_);
lean_ctor_set(v_ictx_1325_, 2, v___y_1314_);
lean_ctor_set(v_ictx_1325_, 3, v___y_1322_);
lean_inc(v___y_1320_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1315_);
v_pmctx_1326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1326_, 0, v_env_1324_);
lean_ctor_set(v_pmctx_1326_, 1, v___y_1315_);
lean_ctor_set(v_pmctx_1326_, 2, v___y_1318_);
lean_ctor_set(v_pmctx_1326_, 3, v___y_1320_);
lean_inc(v___y_1321_);
v_blockCtxt_1327_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1314_, v___y_1321_, v___y_1322_);
v___x_1328_ = l_Lean_Parser_mkParserState(v___y_1312_);
lean_inc_ref(v___x_1328_);
v_s_1329_ = l_Lean_Parser_ParserState_setPos(v___x_1328_, v___y_1321_);
v___x_1330_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_1330_, 0, v_blockCtxt_1327_);
v___x_1331_ = l_Lean_Parser_getTokenTable(v_env_1324_);
lean_inc_ref(v___x_1331_);
lean_inc_ref(v_pmctx_1326_);
lean_inc_ref(v_ictx_1325_);
v_s_1332_ = l_Lean_Parser_ParserFn_run(v___x_1330_, v_ictx_1325_, v_pmctx_1326_, v___x_1331_, v_s_1329_);
lean_inc_ref(v_s_1332_);
v___x_1333_ = l_Lean_Parser_ParserState_allErrors(v_s_1332_);
v___x_1334_ = lean_array_get_size(v___x_1333_);
lean_dec_ref(v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_nat_dec_eq(v___x_1334_, v___x_1335_);
if (v___x_1336_ == 0)
{
v___y_1290_ = v___y_1313_;
v___y_1291_ = v___y_1312_;
v___y_1292_ = v___x_1328_;
v___y_1293_ = v___y_1314_;
v___y_1294_ = v___x_1331_;
v___y_1295_ = v_ictx_1325_;
v___y_1296_ = v___y_1316_;
v___y_1297_ = v___y_1317_;
v___y_1298_ = v___y_1319_;
v___y_1299_ = v_s_1332_;
v___y_1300_ = v_pmctx_1326_;
v___y_1301_ = v___x_1336_;
goto v___jp_1289_;
}
else
{
lean_object* v_pos_1337_; uint8_t v___x_1338_; 
v_pos_1337_ = lean_ctor_get(v_s_1332_, 2);
lean_inc(v_pos_1337_);
v___x_1338_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1325_, v_pos_1337_);
lean_dec(v_pos_1337_);
if (v___x_1338_ == 0)
{
v___y_1290_ = v___y_1313_;
v___y_1291_ = v___y_1312_;
v___y_1292_ = v___x_1328_;
v___y_1293_ = v___y_1314_;
v___y_1294_ = v___x_1331_;
v___y_1295_ = v_ictx_1325_;
v___y_1296_ = v___y_1316_;
v___y_1297_ = v___y_1317_;
v___y_1298_ = v___y_1319_;
v___y_1299_ = v_s_1332_;
v___y_1300_ = v_pmctx_1326_;
v___y_1301_ = v___x_1336_;
goto v___jp_1289_;
}
else
{
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v_pmctx_1326_);
lean_dec(v___y_1317_);
v___y_1235_ = v___y_1313_;
v___y_1236_ = v___y_1312_;
v___y_1237_ = v___y_1314_;
v___y_1238_ = v___y_1316_;
v___y_1239_ = v_ictx_1325_;
v___y_1240_ = v___y_1319_;
v___y_1241_ = v_s_1332_;
goto v___jp_1234_;
}
}
}
v___jp_1339_:
{
lean_object* v_fileName_1340_; lean_object* v_fileMap_1341_; lean_object* v_options_1342_; lean_object* v_currNamespace_1343_; lean_object* v_openDecls_1344_; uint8_t v_suppressElabErrors_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v_fileName_1340_ = lean_ctor_get(v___y_1193_, 0);
v_fileMap_1341_ = lean_ctor_get(v___y_1193_, 1);
v_options_1342_ = lean_ctor_get(v___y_1193_, 2);
v_currNamespace_1343_ = lean_ctor_get(v___y_1193_, 6);
v_openDecls_1344_ = lean_ctor_get(v___y_1193_, 7);
v_suppressElabErrors_1345_ = lean_ctor_get_uint8(v___y_1193_, sizeof(void*)*14 + 1);
v___x_1346_ = lean_unsigned_to_nat(1u);
v___x_1347_ = l_Lean_Syntax_getArg(v_docComment_1188_, v___x_1346_);
v___x_1348_ = 1;
v___x_1349_ = l_Lean_Syntax_getPos_x3f(v___x_1347_, v___x_1348_);
if (lean_obj_tag(v___x_1349_) == 1)
{
lean_object* v_val_1350_; lean_object* v___x_1351_; 
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = l_Lean_Syntax_getTailPos_x3f(v___x_1347_, v___x_1348_);
lean_dec(v___x_1347_);
if (lean_obj_tag(v___x_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v_source_1353_; lean_object* v___x_1354_; lean_object* v_endPos_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
lean_dec(v_docComment_1188_);
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref(v___x_1351_);
v_source_1353_ = lean_ctor_get(v_fileMap_1341_, 0);
v___x_1354_ = lean_string_utf8_prev(v_source_1353_, v_val_1352_);
lean_dec(v_val_1352_);
v_endPos_1355_ = lean_string_utf8_prev(v_source_1353_, v___x_1354_);
lean_dec(v___x_1354_);
v___x_1356_ = lean_string_utf8_byte_size(v_source_1353_);
v___x_1357_ = lean_nat_dec_le(v_endPos_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v_endPos_1355_);
v___y_1312_ = v_source_1353_;
v___y_1313_ = v_suppressElabErrors_1345_;
v___y_1314_ = v_fileMap_1341_;
v___y_1315_ = v_options_1342_;
v___y_1316_ = v_suppressElabErrors_1345_;
v___y_1317_ = v___x_1346_;
v___y_1318_ = v_currNamespace_1343_;
v___y_1319_ = v_fileName_1340_;
v___y_1320_ = v_openDecls_1344_;
v___y_1321_ = v_val_1350_;
v___y_1322_ = v___x_1356_;
goto v___jp_1311_;
}
else
{
v___y_1312_ = v_source_1353_;
v___y_1313_ = v_suppressElabErrors_1345_;
v___y_1314_ = v_fileMap_1341_;
v___y_1315_ = v_options_1342_;
v___y_1316_ = v_suppressElabErrors_1345_;
v___y_1317_ = v___x_1346_;
v___y_1318_ = v_currNamespace_1343_;
v___y_1319_ = v_fileName_1340_;
v___y_1320_ = v_openDecls_1344_;
v___y_1321_ = v_val_1350_;
v___y_1322_ = v_endPos_1355_;
goto v___jp_1311_;
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v___x_1351_);
lean_dec(v_val_1350_);
v___x_1358_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1359_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1188_, v___x_1358_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v_docComment_1188_);
return v___x_1359_;
}
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v___x_1349_);
lean_dec(v___x_1347_);
v___x_1360_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1361_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1188_, v___x_1360_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v_docComment_1188_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1417_, lean_object* v_binders_1418_, lean_object* v_docComment_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1444_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1444_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1444_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 1)
{
lean_object* v_val_1432_; lean_object* v___x_1433_; size_t v_sz_1434_; size_t v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
lean_del_object(v___x_1430_);
v_val_1432_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_val_1432_);
lean_dec_ref(v_a_1428_);
v___x_1433_ = l_Lean_Syntax_getArgs(v_val_1432_);
lean_dec(v_val_1432_);
v_sz_1434_ = lean_array_size(v___x_1433_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_1434_, v___x_1435_, v___x_1433_);
v___x_1437_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1437_, 0, v___x_1436_);
v___x_1438_ = 0;
v___x_1439_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1417_, v_binders_1418_, v___x_1437_, v___x_1438_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec(v_a_1428_);
lean_dec(v_binders_1418_);
lean_dec(v_declName_1417_);
v___x_1440_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1440_);
v___x_1442_ = v___x_1430_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_binders_1418_);
lean_dec(v_declName_1417_);
v_a_1445_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1427_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1427_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1453_, lean_object* v_binders_1454_, lean_object* v_docComment_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_versoDocString(v_declName_1453_, v_binders_1454_, v_docComment_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1460_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_1464_, lean_object* v___x_1465_, lean_object* v_as_1466_, size_t v_sz_1467_, size_t v_i_1468_, lean_object* v_b_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1464_, v___x_1465_, v_as_1466_, v_sz_1467_, v_i_1468_, v_b_1469_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v_as_1480_, lean_object* v_sz_1481_, lean_object* v_i_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
size_t v_sz_boxed_1491_; size_t v_i_boxed_1492_; lean_object* v_res_1493_; 
v_sz_boxed_1491_ = lean_unbox_usize(v_sz_1481_);
lean_dec(v_sz_1481_);
v_i_boxed_1492_ = lean_unbox_usize(v_i_1482_);
lean_dec(v_i_1482_);
v_res_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_1478_, v___x_1479_, v_as_1480_, v_sz_boxed_1491_, v_i_boxed_1492_, v_b_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v_as_1480_);
lean_dec(v___x_1479_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1495_, v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_ref_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_1505_, v_ref_1506_, v_msg_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v_ref_1506_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1516_, lean_object* v_msg_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_msg_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_1526_, v_msg_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_1536_, lean_object* v_macroStack_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1536_, v_macroStack_1537_, v___y_1542_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_1546_, lean_object* v_macroStack_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_1546_, v_macroStack_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t v_sz_1556_, size_t v_i_1557_, lean_object* v_bs_1558_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_usize_dec_lt(v_i_1557_, v_sz_1556_);
if (v___x_1559_ == 0)
{
return v_bs_1558_;
}
else
{
lean_object* v_v_1560_; lean_object* v___x_1561_; lean_object* v_bs_x27_1562_; size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v_v_1560_ = lean_array_uget(v_bs_1558_, v_i_1557_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v_bs_x27_1562_ = lean_array_uset(v_bs_1558_, v_i_1557_, v___x_1561_);
v___x_1563_ = ((size_t)1ULL);
v___x_1564_ = lean_usize_add(v_i_1557_, v___x_1563_);
v___x_1565_ = lean_array_uset(v_bs_x27_1562_, v_i_1557_, v_v_1560_);
v_i_1557_ = v___x_1564_;
v_bs_1558_ = v___x_1565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object* v_sz_1567_, lean_object* v_i_1568_, lean_object* v_bs_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1567_);
lean_dec(v_sz_1567_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1568_);
lean_dec(v_i_1568_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_1570_, v_i_boxed_1571_, v_bs_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1573_, lean_object* v_doc_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1590_; lean_object* v_env_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1582_ = lean_st_ref_get(v_a_1580_);
v_env_1597_ = lean_ctor_get(v___x_1582_, 0);
lean_inc_ref(v_env_1597_);
lean_dec(v___x_1582_);
v___x_1598_ = l_Lean_getMainVersoModuleDocs(v_env_1597_);
v___x_1599_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1598_);
lean_dec_ref(v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
v___y_1590_ = v___x_1599_;
goto v___jp_1589_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1609_; 
v_val_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1609_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_val_1600_, v___x_1604_);
lean_dec(v_val_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1605_);
v___x_1607_ = v___x_1602_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
v___y_1590_ = v___x_1607_;
goto v___jp_1589_;
}
}
}
v___jp_1583_:
{
lean_object* v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1586_, 0, v_range_1573_);
lean_closure_set(v___x_1586_, 1, v___y_1584_);
lean_closure_set(v___x_1586_, 2, v___y_1585_);
v___x_1587_ = 0;
v___x_1588_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1586_, v___x_1587_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
return v___x_1588_;
}
v___jp_1589_:
{
lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_Syntax_getArgs(v_doc_1574_);
v_sz_1592_ = lean_array_size(v___x_1591_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_1592_, v___x_1593_, v___x_1591_);
if (lean_obj_tag(v___y_1590_) == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___y_1584_ = v___x_1594_;
v___y_1585_ = v___x_1595_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1596_; 
v_val_1596_ = lean_ctor_get(v___y_1590_, 0);
lean_inc(v_val_1596_);
lean_dec_ref(v___y_1590_);
v___y_1584_ = v___x_1594_;
v___y_1585_ = v_val_1596_;
goto v___jp_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1610_, lean_object* v_doc_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_versoModDocString(v_range_1610_, v_doc_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_doc_1611_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object* v___x_1620_, lean_object* v_declName_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, uint8_t v___x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_fileName_1632_; lean_object* v_options_1633_; lean_object* v_currRecDepth_1634_; lean_object* v_maxRecDepth_1635_; lean_object* v_ref_1636_; lean_object* v_currNamespace_1637_; lean_object* v_openDecls_1638_; lean_object* v_initHeartbeats_1639_; lean_object* v_maxHeartbeats_1640_; lean_object* v_quotContext_1641_; lean_object* v_currMacroScope_1642_; uint8_t v_diag_1643_; lean_object* v_cancelTk_x3f_1644_; uint8_t v_suppressElabErrors_1645_; lean_object* v_inheritedTraceOptions_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_fileName_1632_ = lean_ctor_get(v___y_1629_, 0);
v_options_1633_ = lean_ctor_get(v___y_1629_, 2);
v_currRecDepth_1634_ = lean_ctor_get(v___y_1629_, 3);
v_maxRecDepth_1635_ = lean_ctor_get(v___y_1629_, 4);
v_ref_1636_ = lean_ctor_get(v___y_1629_, 5);
v_currNamespace_1637_ = lean_ctor_get(v___y_1629_, 6);
v_openDecls_1638_ = lean_ctor_get(v___y_1629_, 7);
v_initHeartbeats_1639_ = lean_ctor_get(v___y_1629_, 8);
v_maxHeartbeats_1640_ = lean_ctor_get(v___y_1629_, 9);
v_quotContext_1641_ = lean_ctor_get(v___y_1629_, 10);
v_currMacroScope_1642_ = lean_ctor_get(v___y_1629_, 11);
v_diag_1643_ = lean_ctor_get_uint8(v___y_1629_, sizeof(void*)*14);
v_cancelTk_x3f_1644_ = lean_ctor_get(v___y_1629_, 12);
v_suppressElabErrors_1645_ = lean_ctor_get_uint8(v___y_1629_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1646_ = lean_ctor_get(v___y_1629_, 13);
lean_inc_ref(v_inheritedTraceOptions_1646_);
lean_inc(v_cancelTk_x3f_1644_);
lean_inc(v_currMacroScope_1642_);
lean_inc(v_quotContext_1641_);
lean_inc(v_maxHeartbeats_1640_);
lean_inc(v_initHeartbeats_1639_);
lean_inc(v_openDecls_1638_);
lean_inc(v_currNamespace_1637_);
lean_inc(v_ref_1636_);
lean_inc(v_maxRecDepth_1635_);
lean_inc(v_currRecDepth_1634_);
lean_inc_ref(v_options_1633_);
lean_inc_ref(v_fileName_1632_);
v___x_1647_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1647_, 0, v_fileName_1632_);
lean_ctor_set(v___x_1647_, 1, v___x_1620_);
lean_ctor_set(v___x_1647_, 2, v_options_1633_);
lean_ctor_set(v___x_1647_, 3, v_currRecDepth_1634_);
lean_ctor_set(v___x_1647_, 4, v_maxRecDepth_1635_);
lean_ctor_set(v___x_1647_, 5, v_ref_1636_);
lean_ctor_set(v___x_1647_, 6, v_currNamespace_1637_);
lean_ctor_set(v___x_1647_, 7, v_openDecls_1638_);
lean_ctor_set(v___x_1647_, 8, v_initHeartbeats_1639_);
lean_ctor_set(v___x_1647_, 9, v_maxHeartbeats_1640_);
lean_ctor_set(v___x_1647_, 10, v_quotContext_1641_);
lean_ctor_set(v___x_1647_, 11, v_currMacroScope_1642_);
lean_ctor_set(v___x_1647_, 12, v_cancelTk_x3f_1644_);
lean_ctor_set(v___x_1647_, 13, v_inheritedTraceOptions_1646_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*14, v_diag_1643_);
lean_ctor_set_uint8(v___x_1647_, sizeof(void*)*14 + 1, v_suppressElabErrors_1645_);
v___x_1648_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1621_, v___x_1622_, v___x_1623_, v___x_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___x_1647_, v___y_1630_);
lean_dec_ref(v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object* v___x_1649_, lean_object* v_declName_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
uint8_t v___x_15625__boxed_1661_; lean_object* v_res_1662_; 
v___x_15625__boxed_1661_ = lean_unbox(v___x_1653_);
v_res_1662_ = l_Lean_versoDocStringFromString___lam__0(v___x_1649_, v_declName_1650_, v___x_1651_, v___x_1652_, v___x_15625__boxed_1661_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1662_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t v___y_1663_, uint8_t v_suppressElabErrors_1664_, lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 1)
{
lean_object* v_pre_1666_; 
v_pre_1666_ = lean_ctor_get(v_x_1665_, 0);
switch(lean_obj_tag(v_pre_1666_))
{
case 1:
{
lean_object* v_pre_1667_; 
v_pre_1667_ = lean_ctor_get(v_pre_1666_, 0);
switch(lean_obj_tag(v_pre_1667_))
{
case 0:
{
lean_object* v_str_1668_; lean_object* v_str_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_str_1668_ = lean_ctor_get(v_x_1665_, 1);
v_str_1669_ = lean_ctor_get(v_pre_1666_, 1);
v___x_1670_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_1671_ = lean_string_dec_eq(v_str_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_1673_ = lean_string_dec_eq(v_str_1669_, v___x_1672_);
if (v___x_1673_ == 0)
{
return v___y_1663_;
}
else
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_1675_ = lean_string_dec_eq(v_str_1668_, v___x_1674_);
if (v___x_1675_ == 0)
{
return v___y_1663_;
}
else
{
return v_suppressElabErrors_1664_;
}
}
}
else
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_1677_ = lean_string_dec_eq(v_str_1668_, v___x_1676_);
if (v___x_1677_ == 0)
{
return v___y_1663_;
}
else
{
return v_suppressElabErrors_1664_;
}
}
}
case 1:
{
lean_object* v_pre_1678_; 
v_pre_1678_ = lean_ctor_get(v_pre_1667_, 0);
if (lean_obj_tag(v_pre_1678_) == 0)
{
lean_object* v_str_1679_; lean_object* v_str_1680_; lean_object* v_str_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_str_1679_ = lean_ctor_get(v_x_1665_, 1);
v_str_1680_ = lean_ctor_get(v_pre_1666_, 1);
v_str_1681_ = lean_ctor_get(v_pre_1667_, 1);
v___x_1682_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_1683_ = lean_string_dec_eq(v_str_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
return v___y_1663_;
}
else
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_1685_ = lean_string_dec_eq(v_str_1680_, v___x_1684_);
if (v___x_1685_ == 0)
{
return v___y_1663_;
}
else
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_1687_ = lean_string_dec_eq(v_str_1679_, v___x_1686_);
if (v___x_1687_ == 0)
{
return v___y_1663_;
}
else
{
return v_suppressElabErrors_1664_;
}
}
}
}
else
{
return v___y_1663_;
}
}
default: 
{
return v___y_1663_;
}
}
}
case 0:
{
lean_object* v_str_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_str_1688_ = lean_ctor_get(v_x_1665_, 1);
v___x_1689_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_1690_ = lean_string_dec_eq(v_str_1688_, v___x_1689_);
if (v___x_1690_ == 0)
{
return v___y_1663_;
}
else
{
return v_suppressElabErrors_1664_;
}
}
default: 
{
return v___y_1663_;
}
}
}
else
{
return v___y_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object* v___y_1691_, lean_object* v_suppressElabErrors_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v___y_15667__boxed_1694_; uint8_t v_suppressElabErrors_boxed_1695_; uint8_t v_res_1696_; lean_object* v_r_1697_; 
v___y_15667__boxed_1694_ = lean_unbox(v___y_1691_);
v_suppressElabErrors_boxed_1695_ = lean_unbox(v_suppressElabErrors_1692_);
v_res_1696_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(v___y_15667__boxed_1694_, v_suppressElabErrors_boxed_1695_, v_x_1693_);
lean_dec(v_x_1693_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object* v_ref_1698_, lean_object* v_msgData_1699_, uint8_t v_severity_1700_, uint8_t v_isSilent_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___y_1708_; uint8_t v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1745_; uint8_t v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; uint8_t v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1781_; uint8_t v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; uint8_t v___y_1787_; uint8_t v___x_1792_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; uint8_t v___y_1799_; uint8_t v___y_1800_; uint8_t v___y_1802_; uint8_t v___x_1817_; 
v___x_1792_ = 2;
v___x_1817_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1700_, v___x_1792_);
if (v___x_1817_ == 0)
{
v___y_1802_ = v___x_1817_;
goto v___jp_1801_;
}
else
{
uint8_t v___x_1818_; 
lean_inc_ref(v_msgData_1699_);
v___x_1818_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1699_);
v___y_1802_ = v___x_1818_;
goto v___jp_1801_;
}
v___jp_1707_:
{
lean_object* v___x_1717_; lean_object* v_currNamespace_1718_; lean_object* v_openDecls_1719_; lean_object* v_env_1720_; lean_object* v_nextMacroScope_1721_; lean_object* v_ngen_1722_; lean_object* v_auxDeclNGen_1723_; lean_object* v_traceState_1724_; lean_object* v_cache_1725_; lean_object* v_messages_1726_; lean_object* v_infoState_1727_; lean_object* v_snapshotTasks_1728_; lean_object* v_newDecls_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1743_; 
v___x_1717_ = lean_st_ref_take(v___y_1716_);
v_currNamespace_1718_ = lean_ctor_get(v___y_1715_, 6);
v_openDecls_1719_ = lean_ctor_get(v___y_1715_, 7);
v_env_1720_ = lean_ctor_get(v___x_1717_, 0);
v_nextMacroScope_1721_ = lean_ctor_get(v___x_1717_, 1);
v_ngen_1722_ = lean_ctor_get(v___x_1717_, 2);
v_auxDeclNGen_1723_ = lean_ctor_get(v___x_1717_, 3);
v_traceState_1724_ = lean_ctor_get(v___x_1717_, 4);
v_cache_1725_ = lean_ctor_get(v___x_1717_, 5);
v_messages_1726_ = lean_ctor_get(v___x_1717_, 6);
v_infoState_1727_ = lean_ctor_get(v___x_1717_, 7);
v_snapshotTasks_1728_ = lean_ctor_get(v___x_1717_, 8);
v_newDecls_1729_ = lean_ctor_get(v___x_1717_, 9);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1731_ = v___x_1717_;
v_isShared_1732_ = v_isSharedCheck_1743_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_newDecls_1729_);
lean_inc(v_snapshotTasks_1728_);
lean_inc(v_infoState_1727_);
lean_inc(v_messages_1726_);
lean_inc(v_cache_1725_);
lean_inc(v_traceState_1724_);
lean_inc(v_auxDeclNGen_1723_);
lean_inc(v_ngen_1722_);
lean_inc(v_nextMacroScope_1721_);
lean_inc(v_env_1720_);
lean_dec(v___x_1717_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1743_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_inc(v_openDecls_1719_);
lean_inc(v_currNamespace_1718_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_currNamespace_1718_);
lean_ctor_set(v___x_1733_, 1, v_openDecls_1719_);
v___x_1734_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
lean_ctor_set(v___x_1734_, 1, v___y_1712_);
lean_inc_ref(v___y_1713_);
lean_inc_ref(v___y_1714_);
v___x_1735_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1735_, 0, v___y_1714_);
lean_ctor_set(v___x_1735_, 1, v___y_1711_);
lean_ctor_set(v___x_1735_, 2, v___y_1708_);
lean_ctor_set(v___x_1735_, 3, v___y_1713_);
lean_ctor_set(v___x_1735_, 4, v___x_1734_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*5, v___y_1709_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*5 + 1, v___y_1710_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*5 + 2, v_isSilent_1701_);
v___x_1736_ = l_Lean_MessageLog_add(v___x_1735_, v_messages_1726_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 6, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_env_1720_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_nextMacroScope_1721_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_ngen_1722_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_auxDeclNGen_1723_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_traceState_1724_);
lean_ctor_set(v_reuseFailAlloc_1742_, 5, v_cache_1725_);
lean_ctor_set(v_reuseFailAlloc_1742_, 6, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1742_, 7, v_infoState_1727_);
lean_ctor_set(v_reuseFailAlloc_1742_, 8, v_snapshotTasks_1728_);
lean_ctor_set(v_reuseFailAlloc_1742_, 9, v_newDecls_1729_);
v___x_1738_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = lean_st_ref_set(v___y_1716_, v___x_1738_);
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
return v___x_1741_;
}
}
}
v___jp_1744_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1768_; 
v___x_1753_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1699_);
v___x_1754_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_1753_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
lean_inc_ref_n(v___y_1750_, 2);
v___x_1759_ = l_Lean_FileMap_toPosition(v___y_1750_, v___y_1748_);
lean_dec(v___y_1748_);
v___x_1760_ = l_Lean_FileMap_toPosition(v___y_1750_, v___y_1752_);
lean_dec(v___y_1752_);
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1746_ == 0)
{
lean_del_object(v___x_1757_);
lean_dec_ref(v___y_1745_);
v___y_1708_ = v___x_1761_;
v___y_1709_ = v___y_1747_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___x_1759_;
v___y_1712_ = v_a_1755_;
v___y_1713_ = v___x_1762_;
v___y_1714_ = v___y_1751_;
v___y_1715_ = v___y_1704_;
v___y_1716_ = v___y_1705_;
goto v___jp_1707_;
}
else
{
uint8_t v___x_1763_; 
lean_inc(v_a_1755_);
v___x_1763_ = l_Lean_MessageData_hasTag(v___y_1745_, v_a_1755_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_dec_ref(v___x_1761_);
lean_dec_ref(v___x_1759_);
lean_dec(v_a_1755_);
v___x_1764_ = lean_box(0);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1764_);
v___x_1766_ = v___x_1757_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_del_object(v___x_1757_);
v___y_1708_ = v___x_1761_;
v___y_1709_ = v___y_1747_;
v___y_1710_ = v___y_1749_;
v___y_1711_ = v___x_1759_;
v___y_1712_ = v_a_1755_;
v___y_1713_ = v___x_1762_;
v___y_1714_ = v___y_1751_;
v___y_1715_ = v___y_1704_;
v___y_1716_ = v___y_1705_;
goto v___jp_1707_;
}
}
}
}
v___jp_1769_:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Syntax_getTailPos_x3f(v___y_1772_, v___y_1773_);
lean_dec(v___y_1772_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_inc(v___y_1777_);
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1773_;
v___y_1748_ = v___y_1777_;
v___y_1749_ = v___y_1774_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v___y_1777_;
goto v___jp_1744_;
}
else
{
lean_object* v_val_1779_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref(v___x_1778_);
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1773_;
v___y_1748_ = v___y_1777_;
v___y_1749_ = v___y_1774_;
v___y_1750_ = v___y_1775_;
v___y_1751_ = v___y_1776_;
v___y_1752_ = v_val_1779_;
goto v___jp_1744_;
}
}
v___jp_1780_:
{
lean_object* v_ref_1788_; lean_object* v___x_1789_; 
v_ref_1788_ = l_Lean_replaceRef(v_ref_1698_, v___y_1784_);
v___x_1789_ = l_Lean_Syntax_getPos_x3f(v_ref_1788_, v___y_1783_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_unsigned_to_nat(0u);
v___y_1770_ = v___y_1781_;
v___y_1771_ = v___y_1782_;
v___y_1772_ = v_ref_1788_;
v___y_1773_ = v___y_1783_;
v___y_1774_ = v___y_1787_;
v___y_1775_ = v___y_1785_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v___x_1790_;
goto v___jp_1769_;
}
else
{
lean_object* v_val_1791_; 
v_val_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_val_1791_);
lean_dec_ref(v___x_1789_);
v___y_1770_ = v___y_1781_;
v___y_1771_ = v___y_1782_;
v___y_1772_ = v_ref_1788_;
v___y_1773_ = v___y_1783_;
v___y_1774_ = v___y_1787_;
v___y_1775_ = v___y_1785_;
v___y_1776_ = v___y_1786_;
v___y_1777_ = v_val_1791_;
goto v___jp_1769_;
}
}
v___jp_1793_:
{
if (v___y_1800_ == 0)
{
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1799_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v___y_1797_;
v___y_1786_ = v___y_1798_;
v___y_1787_ = v_severity_1700_;
goto v___jp_1780_;
}
else
{
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1799_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v___y_1797_;
v___y_1786_ = v___y_1798_;
v___y_1787_ = v___x_1792_;
goto v___jp_1780_;
}
}
v___jp_1801_:
{
if (v___y_1802_ == 0)
{
lean_object* v_fileName_1803_; lean_object* v_fileMap_1804_; lean_object* v_options_1805_; lean_object* v_ref_1806_; uint8_t v_suppressElabErrors_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___f_1810_; uint8_t v___x_1811_; uint8_t v___x_1812_; 
v_fileName_1803_ = lean_ctor_get(v___y_1704_, 0);
v_fileMap_1804_ = lean_ctor_get(v___y_1704_, 1);
v_options_1805_ = lean_ctor_get(v___y_1704_, 2);
v_ref_1806_ = lean_ctor_get(v___y_1704_, 5);
v_suppressElabErrors_1807_ = lean_ctor_get_uint8(v___y_1704_, sizeof(void*)*14 + 1);
v___x_1808_ = lean_box(v___y_1802_);
v___x_1809_ = lean_box(v_suppressElabErrors_1807_);
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1810_, 0, v___x_1808_);
lean_closure_set(v___f_1810_, 1, v___x_1809_);
v___x_1811_ = 1;
v___x_1812_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1700_, v___x_1811_);
if (v___x_1812_ == 0)
{
v___y_1794_ = v_suppressElabErrors_1807_;
v___y_1795_ = v_ref_1806_;
v___y_1796_ = v___f_1810_;
v___y_1797_ = v_fileMap_1804_;
v___y_1798_ = v_fileName_1803_;
v___y_1799_ = v___y_1802_;
v___y_1800_ = v___x_1812_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = l_Lean_warningAsError;
v___x_1814_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1805_, v___x_1813_);
v___y_1794_ = v_suppressElabErrors_1807_;
v___y_1795_ = v_ref_1806_;
v___y_1796_ = v___f_1810_;
v___y_1797_ = v_fileMap_1804_;
v___y_1798_ = v_fileName_1803_;
v___y_1799_ = v___y_1802_;
v___y_1800_ = v___x_1814_;
goto v___jp_1793_;
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec_ref(v_msgData_1699_);
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object* v_ref_1819_, lean_object* v_msgData_1820_, lean_object* v_severity_1821_, lean_object* v_isSilent_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v_severity_boxed_1828_; uint8_t v_isSilent_boxed_1829_; lean_object* v_res_1830_; 
v_severity_boxed_1828_ = lean_unbox(v_severity_1821_);
v_isSilent_boxed_1829_ = lean_unbox(v_isSilent_1822_);
v_res_1830_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1819_, v_msgData_1820_, v_severity_boxed_1828_, v_isSilent_boxed_1829_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v_ref_1819_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object* v_as_1831_, size_t v_sz_1832_, size_t v_i_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1833_, v_sz_1832_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1834_);
return v___x_1843_;
}
else
{
lean_object* v_ref_1844_; lean_object* v_a_1845_; uint8_t v_severity_1846_; lean_object* v_data_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v_ref_1844_ = lean_ctor_get(v___y_1839_, 5);
v_a_1845_ = lean_array_uget_borrowed(v_as_1831_, v_i_1833_);
v_severity_1846_ = lean_ctor_get_uint8(v_a_1845_, sizeof(void*)*5 + 1);
v_data_1847_ = lean_ctor_get(v_a_1845_, 4);
v___x_1848_ = 0;
lean_inc(v_data_1847_);
v___x_1849_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1844_, v_data_1847_, v_severity_1846_, v___x_1848_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; 
lean_dec_ref(v___x_1849_);
v___x_1850_ = lean_box(0);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = lean_usize_add(v_i_1833_, v___x_1851_);
v_i_1833_ = v___x_1852_;
v_b_1834_ = v___x_1850_;
goto _start;
}
else
{
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object* v_as_1854_, lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_b_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
size_t v_sz_boxed_1865_; size_t v_i_boxed_1866_; lean_object* v_res_1867_; 
v_sz_boxed_1865_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1866_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_1854_, v_sz_boxed_1865_, v_i_boxed_1866_, v_b_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec_ref(v_as_1854_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t v_flag_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v_infoState_1872_; lean_object* v_env_1873_; lean_object* v_nextMacroScope_1874_; lean_object* v_ngen_1875_; lean_object* v_auxDeclNGen_1876_; lean_object* v_traceState_1877_; lean_object* v_cache_1878_; lean_object* v_messages_1879_; lean_object* v_snapshotTasks_1880_; lean_object* v_newDecls_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1901_; 
v___x_1871_ = lean_st_ref_take(v___y_1869_);
v_infoState_1872_ = lean_ctor_get(v___x_1871_, 7);
v_env_1873_ = lean_ctor_get(v___x_1871_, 0);
v_nextMacroScope_1874_ = lean_ctor_get(v___x_1871_, 1);
v_ngen_1875_ = lean_ctor_get(v___x_1871_, 2);
v_auxDeclNGen_1876_ = lean_ctor_get(v___x_1871_, 3);
v_traceState_1877_ = lean_ctor_get(v___x_1871_, 4);
v_cache_1878_ = lean_ctor_get(v___x_1871_, 5);
v_messages_1879_ = lean_ctor_get(v___x_1871_, 6);
v_snapshotTasks_1880_ = lean_ctor_get(v___x_1871_, 8);
v_newDecls_1881_ = lean_ctor_get(v___x_1871_, 9);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1883_ = v___x_1871_;
v_isShared_1884_ = v_isSharedCheck_1901_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_newDecls_1881_);
lean_inc(v_snapshotTasks_1880_);
lean_inc(v_infoState_1872_);
lean_inc(v_messages_1879_);
lean_inc(v_cache_1878_);
lean_inc(v_traceState_1877_);
lean_inc(v_auxDeclNGen_1876_);
lean_inc(v_ngen_1875_);
lean_inc(v_nextMacroScope_1874_);
lean_inc(v_env_1873_);
lean_dec(v___x_1871_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1901_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_assignment_1885_; lean_object* v_lazyAssignment_1886_; lean_object* v_trees_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1900_; 
v_assignment_1885_ = lean_ctor_get(v_infoState_1872_, 0);
v_lazyAssignment_1886_ = lean_ctor_get(v_infoState_1872_, 1);
v_trees_1887_ = lean_ctor_get(v_infoState_1872_, 2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_infoState_1872_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1889_ = v_infoState_1872_;
v_isShared_1890_ = v_isSharedCheck_1900_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_trees_1887_);
lean_inc(v_lazyAssignment_1886_);
lean_inc(v_assignment_1885_);
lean_dec(v_infoState_1872_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1900_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_assignment_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_lazyAssignment_1886_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_trees_1887_);
v___x_1892_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3, v_flag_1868_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 7, v___x_1892_);
v___x_1894_ = v___x_1883_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_env_1873_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_nextMacroScope_1874_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_ngen_1875_);
lean_ctor_set(v_reuseFailAlloc_1898_, 3, v_auxDeclNGen_1876_);
lean_ctor_set(v_reuseFailAlloc_1898_, 4, v_traceState_1877_);
lean_ctor_set(v_reuseFailAlloc_1898_, 5, v_cache_1878_);
lean_ctor_set(v_reuseFailAlloc_1898_, 6, v_messages_1879_);
lean_ctor_set(v_reuseFailAlloc_1898_, 7, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1898_, 8, v_snapshotTasks_1880_);
lean_ctor_set(v_reuseFailAlloc_1898_, 9, v_newDecls_1881_);
v___x_1894_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_st_ref_set(v___y_1869_, v___x_1894_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object* v_flag_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
uint8_t v_flag_boxed_1905_; lean_object* v_res_1906_; 
v_flag_boxed_1905_ = lean_unbox(v_flag_1902_);
v_res_1906_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_1905_, v___y_1903_);
lean_dec(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t v_flag_1907_, lean_object* v_x_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v_infoState_1917_; uint8_t v_enabled_1918_; lean_object* v_a_1920_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1916_ = lean_st_ref_get(v___y_1914_);
v_infoState_1917_ = lean_ctor_get(v___x_1916_, 7);
lean_inc_ref(v_infoState_1917_);
lean_dec(v___x_1916_);
v_enabled_1918_ = lean_ctor_get_uint8(v_infoState_1917_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1917_);
v___x_1930_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_1907_, v___y_1914_);
lean_dec_ref(v___x_1930_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
v___x_1931_ = lean_apply_7(v_x_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, lean_box(0));
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1918_, v___y_1914_);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1933_, 0);
lean_dec(v_unused_1941_);
v___x_1935_ = v___x_1933_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v___x_1933_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v_a_1932_);
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1932_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1931_);
v_a_1920_ = v_a_1942_;
goto v___jp_1919_;
}
v___jp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v___x_1921_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1918_, v___y_1914_);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1921_, 0);
lean_dec(v_unused_1929_);
v___x_1923_ = v___x_1921_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_dec(v___x_1921_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 1);
lean_ctor_set(v___x_1923_, 0, v_a_1920_);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object* v_flag_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v_flag_boxed_1952_; lean_object* v_res_1953_; 
v_flag_boxed_1952_ = lean_unbox(v_flag_1943_);
v_res_1953_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_boxed_1952_, v_x_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object* v_msgData_1954_, uint8_t v_severity_1955_, uint8_t v_isSilent_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_ref_1964_; lean_object* v___x_1965_; 
v_ref_1964_ = lean_ctor_get(v___y_1961_, 5);
v___x_1965_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1964_, v_msgData_1954_, v_severity_1955_, v_isSilent_1956_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object* v_msgData_1966_, lean_object* v_severity_1967_, lean_object* v_isSilent_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
uint8_t v_severity_boxed_1976_; uint8_t v_isSilent_boxed_1977_; lean_object* v_res_1978_; 
v_severity_boxed_1976_ = lean_unbox(v_severity_1967_);
v_isSilent_boxed_1977_ = lean_unbox(v_isSilent_1968_);
v_res_1978_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1966_, v_severity_boxed_1976_, v_isSilent_boxed_1977_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object* v_msgData_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = 2;
v___x_1988_ = 0;
v___x_1989_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1979_, v___x_1987_, v___x_1988_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object* v_msgData_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v_msgData_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2011_, 0, v_b_2002_);
return v___x_2011_;
}
else
{
lean_object* v_a_2012_; lean_object* v_snd_2013_; lean_object* v_snd_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2012_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
v_snd_2013_ = lean_ctor_get(v_a_2012_, 1);
v_snd_2014_ = lean_ctor_get(v_snd_2013_, 1);
lean_inc(v_snd_2014_);
v___x_2015_ = l_Lean_Parser_Error_toString(v_snd_2014_);
v___x_2016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___x_2017_ = l_Lean_MessageData_ofFormat(v___x_2016_);
v___x_2018_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2017_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; 
lean_dec_ref(v___x_2018_);
v___x_2019_ = lean_box(0);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_i_2001_, v___x_2020_);
v_i_2001_ = v___x_2021_;
v_b_2002_ = v___x_2019_;
goto _start;
}
else
{
return v___x_2018_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object* v_as_2023_, lean_object* v_sz_2024_, lean_object* v_i_2025_, lean_object* v_b_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
size_t v_sz_boxed_2034_; size_t v_i_boxed_2035_; lean_object* v_res_2036_; 
v_sz_boxed_2034_ = lean_unbox_usize(v_sz_2024_);
lean_dec(v_sz_2024_);
v_i_boxed_2035_ = lean_unbox_usize(v_i_2025_);
lean_dec(v_i_2025_);
v_res_2036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_2023_, v_sz_boxed_2034_, v_i_boxed_2035_, v_b_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v_as_2023_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2056_, lean_object* v_docComment_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2065_; lean_object* v_env_2066_; lean_object* v_fileName_2067_; lean_object* v_options_2068_; lean_object* v_currNamespace_2069_; lean_object* v_openDecls_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2065_ = lean_st_ref_get(v_a_2063_);
v_env_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref_n(v_env_2066_, 2);
lean_dec(v___x_2065_);
v_fileName_2067_ = lean_ctor_get(v_a_2062_, 0);
v_options_2068_ = lean_ctor_get(v_a_2062_, 2);
v_currNamespace_2069_ = lean_ctor_get(v_a_2062_, 6);
v_openDecls_2070_ = lean_ctor_get(v_a_2062_, 7);
v___x_2071_ = lean_string_utf8_byte_size(v_docComment_2057_);
lean_inc_ref_n(v_docComment_2057_, 2);
v___x_2072_ = l_Lean_FileMap_ofString(v_docComment_2057_);
lean_inc_ref(v___x_2072_);
lean_inc_ref(v_fileName_2067_);
v___x_2073_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2073_, 0, v_docComment_2057_);
lean_ctor_set(v___x_2073_, 1, v_fileName_2067_);
lean_ctor_set(v___x_2073_, 2, v___x_2072_);
lean_ctor_set(v___x_2073_, 3, v___x_2071_);
lean_inc(v_openDecls_2070_);
lean_inc(v_currNamespace_2069_);
lean_inc_ref(v_options_2068_);
v___x_2074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2074_, 0, v_env_2066_);
lean_ctor_set(v___x_2074_, 1, v_options_2068_);
lean_ctor_set(v___x_2074_, 2, v_currNamespace_2069_);
lean_ctor_set(v___x_2074_, 3, v_openDecls_2070_);
v___x_2075_ = l_Lean_Parser_mkParserState(v_docComment_2057_);
lean_dec_ref(v_docComment_2057_);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__2));
v___x_2078_ = l_Lean_Parser_getTokenTable(v_env_2066_);
v___x_2079_ = l_Lean_Parser_ParserFn_run(v___x_2077_, v___x_2073_, v___x_2074_, v___x_2078_, v___x_2075_);
lean_inc_ref(v___x_2079_);
v___x_2080_ = l_Lean_Parser_ParserState_allErrors(v___x_2079_);
v___x_2081_ = lean_array_get_size(v___x_2080_);
v___x_2082_ = lean_nat_dec_eq(v___x_2081_, v___x_2076_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v___x_2079_);
lean_dec_ref(v___x_2072_);
lean_dec(v_declName_2056_);
v___x_2083_ = lean_box(0);
v_sz_2084_ = lean_array_size(v___x_2080_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_2080_, v_sz_2084_, v___x_2085_, v___x_2083_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
lean_dec_ref(v___x_2080_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2094_; 
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v___x_2086_, 0);
lean_dec(v_unused_2095_);
v___x_2088_ = v___x_2086_;
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
else
{
lean_dec(v___x_2086_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2094_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2090_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2090_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_a_2096_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2086_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2086_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v___x_2104_; 
lean_dec_ref(v___x_2080_);
v___x_2104_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v_a_2107_; lean_object* v_stxStack_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; size_t v_sz_2130_; size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v_stxStack_2125_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_ref(v_stxStack_2125_);
lean_dec_ref(v___x_2079_);
v___x_2126_ = 0;
v___x_2127_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2125_);
lean_dec_ref(v_stxStack_2125_);
v___x_2128_ = l_Lean_Syntax_getArgs(v___x_2127_);
lean_dec(v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__6));
v_sz_2130_ = lean_array_size(v___x_2128_);
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_2130_, v___x_2131_, v___x_2128_);
v___x_2133_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2133_, 0, v___x_2132_);
v___x_2134_ = 1;
v___x_2135_ = lean_box(v___x_2134_);
v___f_2136_ = lean_alloc_closure((void*)(l_Lean_versoDocStringFromString___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2136_, 0, v___x_2072_);
lean_closure_set(v___f_2136_, 1, v_declName_2056_);
lean_closure_set(v___f_2136_, 2, v___x_2129_);
lean_closure_set(v___f_2136_, 3, v___x_2133_);
lean_closure_set(v___f_2136_, 4, v___x_2135_);
v___x_2137_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_2126_, v___f_2136_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2063_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = l_Lean_Core_setMessageLog___redArg(v_a_2105_, v_a_2063_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; size_t v_sz_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v___x_2141_);
v___x_2142_ = l_Lean_MessageLog_toArray(v_a_2140_);
lean_dec(v_a_2140_);
v___x_2143_ = lean_box(0);
v_sz_2144_ = lean_array_size(v___x_2142_);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_2142_, v_sz_2144_, v___x_2131_, v___x_2143_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_);
lean_dec_ref(v___x_2142_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2145_, 0);
lean_dec(v_unused_2153_);
v___x_2147_ = v___x_2145_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_dec(v___x_2145_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v_a_2138_);
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2138_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_a_2138_);
v_a_2154_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2145_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2145_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_a_2140_);
lean_dec(v_a_2138_);
v_a_2162_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2141_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2141_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; 
lean_dec(v_a_2138_);
v_a_2170_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v___x_2139_);
v_a_2107_ = v_a_2170_;
goto v___jp_2106_;
}
}
else
{
lean_object* v_a_2171_; 
v_a_2171_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2137_);
v_a_2107_ = v_a_2171_;
goto v___jp_2106_;
}
v___jp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Core_setMessageLog___redArg(v_a_2105_, v_a_2063_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2108_, 0);
lean_dec(v_unused_2116_);
v___x_2110_ = v___x_2108_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_dec(v___x_2108_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 1);
lean_ctor_set(v___x_2110_, 0, v_a_2107_);
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2107_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_a_2107_);
v_a_2117_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2108_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_2079_);
lean_dec_ref(v___x_2072_);
lean_dec(v_declName_2056_);
v_a_2172_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2104_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2104_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2180_, lean_object* v_docComment_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_versoDocStringFromString(v_declName_2180_, v_docComment_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t v_flag_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_2190_, v___y_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object* v_flag_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
uint8_t v_flag_boxed_2207_; lean_object* v_res_2208_; 
v_flag_boxed_2207_ = lean_unbox(v_flag_2199_);
v_res_2208_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_2207_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object* v_00_u03b1_2209_, uint8_t v_flag_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_2210_, v_x_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_flag_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
uint8_t v_flag_boxed_2230_; lean_object* v_res_2231_; 
v_flag_boxed_2230_ = lean_unbox(v_flag_2221_);
v_res_2231_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(v_00_u03b1_2220_, v_flag_boxed_2230_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object* v_ref_2232_, lean_object* v_msgData_2233_, uint8_t v_severity_2234_, uint8_t v_isSilent_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2232_, v_msgData_2233_, v_severity_2234_, v_isSilent_2235_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object* v_ref_2244_, lean_object* v_msgData_2245_, lean_object* v_severity_2246_, lean_object* v_isSilent_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v_severity_boxed_2255_; uint8_t v_isSilent_boxed_2256_; lean_object* v_res_2257_; 
v_severity_boxed_2255_ = lean_unbox(v_severity_2246_);
v_isSilent_boxed_2256_ = lean_unbox(v_isSilent_2247_);
v_res_2257_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(v_ref_2244_, v_msgData_2245_, v_severity_boxed_2255_, v_isSilent_boxed_2256_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v_ref_2244_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2258_, lean_object* v_declName_2259_, lean_object* v_env_2260_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = l_Lean_docStringExt;
v___x_2262_ = l_String_removeLeadingSpaces(v_docString_2258_);
v___x_2263_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2261_, v_env_2260_, v_declName_2259_, v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2264_, lean_object* v_modifyEnv_2265_, lean_object* v_docString_2266_){
_start:
{
lean_object* v___f_2267_; lean_object* v___x_2268_; 
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2267_, 0, v_docString_2266_);
lean_closure_set(v___f_2267_, 1, v_declName_2264_);
v___x_2268_ = lean_apply_1(v_modifyEnv_2265_, v___f_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_docComment_2271_, lean_object* v_toBind_2272_, lean_object* v___f_2273_, lean_object* v_____r_2274_){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = l_Lean_getDocStringText___redArg(v_inst_2269_, v_inst_2270_, v_docComment_2271_);
v___x_2276_ = lean_apply_4(v_toBind_2272_, lean_box(0), lean_box(0), v___x_2275_, v___f_2273_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_docComment_2282_, lean_object* v_toBind_2283_, lean_object* v___f_2284_, lean_object* v_____r_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = l_Lean_validateDocComment___redArg(v_inst_2277_, v_inst_2278_, v_inst_2279_, v_inst_2280_, v_inst_2281_, v_docComment_2282_);
v___x_2287_ = lean_apply_4(v_toBind_2283_, lean_box(0), lean_box(0), v___x_2286_, v___f_2284_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_inst_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_docComment_2293_, lean_object* v_toBind_2294_, lean_object* v___f_2295_, lean_object* v_____r_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2288_, v_inst_2289_, v_inst_2290_, v_inst_2291_, v_inst_2292_, v_docComment_2293_, v_toBind_2294_, v___f_2295_, v_____r_2296_);
lean_dec(v_docComment_2293_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2298_, lean_object* v_____r_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_apply_1(v___f_2298_, v_____r_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2307_, lean_object* v_declName_2308_, uint8_t v___x_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_toBind_2312_, lean_object* v___f_2313_, lean_object* v_____do__lift_2314_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2314_, v_declName_2308_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_dec(v___f_2313_);
lean_dec(v_toBind_2312_);
lean_dec_ref(v_inst_2311_);
lean_dec_ref(v_inst_2310_);
lean_dec(v_declName_2308_);
goto v___jp_2315_;
}
else
{
lean_dec_ref(v___x_2318_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec(v___f_2307_);
v___x_2319_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2320_ = l_Lean_MessageData_ofConstName(v_declName_2308_, v___x_2309_);
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2319_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
v___x_2322_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2321_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_throwError___redArg(v_inst_2310_, v_inst_2311_, v___x_2323_);
v___x_2325_ = lean_apply_4(v_toBind_2312_, lean_box(0), lean_box(0), v___x_2324_, v___f_2313_);
return v___x_2325_;
}
else
{
lean_dec(v___f_2313_);
lean_dec(v_toBind_2312_);
lean_dec_ref(v_inst_2311_);
lean_dec_ref(v_inst_2310_);
lean_dec(v_declName_2308_);
goto v___jp_2315_;
}
}
v___jp_2315_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_apply_1(v___f_2307_, v___x_2316_);
return v___x_2317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2326_, lean_object* v_declName_2327_, lean_object* v___x_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_toBind_2331_, lean_object* v___f_2332_, lean_object* v_____do__lift_2333_){
_start:
{
uint8_t v___x_390__boxed_2334_; lean_object* v_res_2335_; 
v___x_390__boxed_2334_ = lean_unbox(v___x_2328_);
v_res_2335_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2326_, v_declName_2327_, v___x_390__boxed_2334_, v_inst_2329_, v_inst_2330_, v_toBind_2331_, v___f_2332_, v_____do__lift_2333_);
lean_dec_ref(v_____do__lift_2333_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_declName_2343_, lean_object* v_docComment_2344_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = l_Lean_Name_isAnonymous(v_declName_2343_);
if (v___x_2345_ == 0)
{
lean_object* v_toBind_2346_; lean_object* v_getEnv_2347_; lean_object* v_modifyEnv_2348_; lean_object* v___f_2349_; lean_object* v___f_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; 
v_toBind_2346_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc_n(v_toBind_2346_, 4);
v_getEnv_2347_ = lean_ctor_get(v_inst_2339_, 0);
lean_inc(v_getEnv_2347_);
v_modifyEnv_2348_ = lean_ctor_get(v_inst_2339_, 1);
lean_inc(v_modifyEnv_2348_);
lean_dec_ref(v_inst_2339_);
lean_inc(v_declName_2343_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2349_, 0, v_declName_2343_);
lean_closure_set(v___f_2349_, 1, v_modifyEnv_2348_);
lean_inc(v_docComment_2344_);
lean_inc_ref(v_inst_2340_);
lean_inc_ref_n(v_inst_2336_, 2);
v___f_2350_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2350_, 0, v_inst_2336_);
lean_closure_set(v___f_2350_, 1, v_inst_2340_);
lean_closure_set(v___f_2350_, 2, v_docComment_2344_);
lean_closure_set(v___f_2350_, 3, v_toBind_2346_);
lean_closure_set(v___f_2350_, 4, v___f_2349_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2351_, 0, v_inst_2336_);
lean_closure_set(v___f_2351_, 1, v_inst_2337_);
lean_closure_set(v___f_2351_, 2, v_inst_2341_);
lean_closure_set(v___f_2351_, 3, v_inst_2342_);
lean_closure_set(v___f_2351_, 4, v_inst_2338_);
lean_closure_set(v___f_2351_, 5, v_docComment_2344_);
lean_closure_set(v___f_2351_, 6, v_toBind_2346_);
lean_closure_set(v___f_2351_, 7, v___f_2350_);
lean_inc_ref(v___f_2351_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2352_, 0, v___f_2351_);
v___x_2353_ = lean_box(v___x_2345_);
v___f_2354_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2354_, 0, v___f_2351_);
lean_closure_set(v___f_2354_, 1, v_declName_2343_);
lean_closure_set(v___f_2354_, 2, v___x_2353_);
lean_closure_set(v___f_2354_, 3, v_inst_2336_);
lean_closure_set(v___f_2354_, 4, v_inst_2340_);
lean_closure_set(v___f_2354_, 5, v_toBind_2346_);
lean_closure_set(v___f_2354_, 6, v___f_2352_);
v___x_2355_ = lean_apply_4(v_toBind_2346_, lean_box(0), lean_box(0), v_getEnv_2347_, v___f_2354_);
return v___x_2355_;
}
else
{
lean_object* v_toApplicative_2356_; lean_object* v_toPure_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_docComment_2344_);
lean_dec(v_declName_2343_);
lean_dec(v_inst_2342_);
lean_dec_ref(v_inst_2341_);
lean_dec_ref(v_inst_2340_);
lean_dec_ref(v_inst_2339_);
lean_dec(v_inst_2338_);
lean_dec(v_inst_2337_);
v_toApplicative_2356_ = lean_ctor_get(v_inst_2336_, 0);
lean_inc_ref(v_toApplicative_2356_);
lean_dec_ref(v_inst_2336_);
v_toPure_2357_ = lean_ctor_get(v_toApplicative_2356_, 1);
lean_inc(v_toPure_2357_);
lean_dec_ref(v_toApplicative_2356_);
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_apply_2(v_toPure_2357_, lean_box(0), v___x_2358_);
return v___x_2359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_declName_2368_, lean_object* v_docComment_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_addMarkdownDocString___redArg(v_inst_2361_, v_inst_2362_, v_inst_2363_, v_inst_2364_, v_inst_2365_, v_inst_2366_, v_inst_2367_, v_declName_2368_, v_docComment_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2371_, lean_object* v_docs_2372_, lean_object* v_env_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = l_Lean_versoDocStringExt;
v___x_2375_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2374_, v_env_2373_, v_declName_2371_, v_docs_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_2376_, lean_object* v___f_2377_, lean_object* v_____r_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_apply_1(v_modifyEnv_2376_, v___f_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_2382_, lean_object* v_modifyEnv_2383_, lean_object* v___f_2384_, uint8_t v___x_2385_, lean_object* v_inst_2386_, lean_object* v_inst_2387_, lean_object* v_toBind_2388_, lean_object* v___f_2389_, lean_object* v_____do__lift_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2390_, v_declName_2382_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; 
lean_dec(v___f_2389_);
lean_dec(v_toBind_2388_);
lean_dec_ref(v_inst_2387_);
lean_dec_ref(v_inst_2386_);
lean_dec(v_declName_2382_);
v___x_2392_ = lean_apply_1(v_modifyEnv_2383_, v___f_2384_);
return v___x_2392_;
}
else
{
lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2409_; 
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v___x_2391_, 0);
lean_dec(v_unused_2410_);
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2409_;
goto v_resetjp_2393_;
}
else
{
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2409_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
if (v___x_2385_ == 0)
{
lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_dec_ref(v___f_2384_);
lean_dec(v_modifyEnv_2383_);
v___x_2396_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2397_ = 1;
v___x_2398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2382_, v___x_2397_);
v___x_2399_ = lean_string_append(v___x_2396_, v___x_2398_);
lean_dec_ref(v___x_2398_);
v___x_2400_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2401_ = lean_string_append(v___x_2399_, v___x_2400_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 3);
lean_ctor_set(v___x_2394_, 0, v___x_2401_);
v___x_2403_ = v___x_2394_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = l_Lean_MessageData_ofFormat(v___x_2403_);
v___x_2405_ = l_Lean_throwError___redArg(v_inst_2386_, v_inst_2387_, v___x_2404_);
v___x_2406_ = lean_apply_4(v_toBind_2388_, lean_box(0), lean_box(0), v___x_2405_, v___f_2389_);
return v___x_2406_;
}
}
else
{
lean_object* v___x_2408_; 
lean_del_object(v___x_2394_);
lean_dec(v___f_2389_);
lean_dec(v_toBind_2388_);
lean_dec_ref(v_inst_2387_);
lean_dec_ref(v_inst_2386_);
lean_dec(v_declName_2382_);
v___x_2408_ = lean_apply_1(v_modifyEnv_2383_, v___f_2384_);
return v___x_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_2411_, lean_object* v_modifyEnv_2412_, lean_object* v___f_2413_, lean_object* v___x_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_toBind_2417_, lean_object* v___f_2418_, lean_object* v_____do__lift_2419_){
_start:
{
uint8_t v___x_304__boxed_2420_; lean_object* v_res_2421_; 
v___x_304__boxed_2420_ = lean_unbox(v___x_2414_);
v_res_2421_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_2411_, v_modifyEnv_2412_, v___f_2413_, v___x_304__boxed_2420_, v_inst_2415_, v_inst_2416_, v_toBind_2417_, v___f_2418_, v_____do__lift_2419_);
lean_dec_ref(v_____do__lift_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_inst_2424_, lean_object* v_declName_2425_, lean_object* v_docs_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = l_Lean_Name_isAnonymous(v_declName_2425_);
if (v___x_2427_ == 0)
{
lean_object* v_toBind_2428_; lean_object* v_getEnv_2429_; lean_object* v_modifyEnv_2430_; lean_object* v___f_2431_; lean_object* v___f_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; 
v_toBind_2428_ = lean_ctor_get(v_inst_2422_, 1);
lean_inc_n(v_toBind_2428_, 2);
v_getEnv_2429_ = lean_ctor_get(v_inst_2423_, 0);
lean_inc(v_getEnv_2429_);
v_modifyEnv_2430_ = lean_ctor_get(v_inst_2423_, 1);
lean_inc_n(v_modifyEnv_2430_, 2);
lean_dec_ref(v_inst_2423_);
lean_inc(v_declName_2425_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2431_, 0, v_declName_2425_);
lean_closure_set(v___f_2431_, 1, v_docs_2426_);
lean_inc_ref(v___f_2431_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2432_, 0, v_modifyEnv_2430_);
lean_closure_set(v___f_2432_, 1, v___f_2431_);
v___x_2433_ = lean_box(v___x_2427_);
v___f_2434_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2434_, 0, v_declName_2425_);
lean_closure_set(v___f_2434_, 1, v_modifyEnv_2430_);
lean_closure_set(v___f_2434_, 2, v___f_2431_);
lean_closure_set(v___f_2434_, 3, v___x_2433_);
lean_closure_set(v___f_2434_, 4, v_inst_2422_);
lean_closure_set(v___f_2434_, 5, v_inst_2424_);
lean_closure_set(v___f_2434_, 6, v_toBind_2428_);
lean_closure_set(v___f_2434_, 7, v___f_2432_);
v___x_2435_ = lean_apply_4(v_toBind_2428_, lean_box(0), lean_box(0), v_getEnv_2429_, v___f_2434_);
return v___x_2435_;
}
else
{
lean_object* v_toApplicative_2436_; lean_object* v_toPure_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_dec_ref(v_docs_2426_);
lean_dec(v_declName_2425_);
lean_dec_ref(v_inst_2424_);
lean_dec_ref(v_inst_2423_);
v_toApplicative_2436_ = lean_ctor_get(v_inst_2422_, 0);
lean_inc_ref(v_toApplicative_2436_);
lean_dec_ref(v_inst_2422_);
v_toPure_2437_ = lean_ctor_get(v_toApplicative_2436_, 1);
lean_inc(v_toPure_2437_);
lean_dec_ref(v_toApplicative_2436_);
v___x_2438_ = lean_box(0);
v___x_2439_ = lean_apply_2(v_toPure_2437_, lean_box(0), v___x_2438_);
return v___x_2439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_declName_2445_, lean_object* v_docs_2446_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2441_, v_inst_2442_, v_inst_2444_, v_declName_2445_, v_docs_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_declName_2453_, lean_object* v_docs_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_addVersoDocStringCore(v_m_2448_, v_inst_2449_, v_inst_2450_, v_inst_2451_, v_inst_2452_, v_declName_2453_, v_docs_2454_);
lean_dec(v_inst_2451_);
return v_res_2455_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_____do__lift_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2463_, v_docs_2459_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v_inst_2462_);
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_2467_ = l_Lean_stringToMessageData(v_a_2465_);
v___x_2468_ = l_Lean_indentD(v___x_2467_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l_Lean_throwError___redArg(v_inst_2460_, v_inst_2461_, v___x_2469_);
return v___x_2470_;
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2472_; 
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_inst_2460_);
v_a_2471_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2464_);
v___x_2472_ = l_Lean_setEnv___redArg(v_inst_2462_, v_a_2471_);
return v___x_2472_;
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2475_ = l_Lean_stringToMessageData(v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_toBind_2478_, lean_object* v_getEnv_2479_, lean_object* v___f_2480_, lean_object* v_____do__lift_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = l_Lean_getMainModuleDoc(v_____do__lift_2481_);
v___x_2483_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2482_);
lean_dec_ref(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v___f_2480_);
lean_dec(v_getEnv_2479_);
lean_dec(v_toBind_2478_);
v___x_2484_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2485_ = l_Lean_throwError___redArg(v_inst_2476_, v_inst_2477_, v___x_2484_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; 
lean_dec_ref(v_inst_2477_);
lean_dec_ref(v_inst_2476_);
v___x_2486_ = lean_apply_4(v_toBind_2478_, lean_box(0), lean_box(0), v_getEnv_2479_, v___f_2480_);
return v___x_2486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_docs_2490_){
_start:
{
lean_object* v_toBind_2491_; lean_object* v_getEnv_2492_; lean_object* v___f_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; 
v_toBind_2491_ = lean_ctor_get(v_inst_2487_, 1);
lean_inc_n(v_toBind_2491_, 2);
v_getEnv_2492_ = lean_ctor_get(v_inst_2488_, 0);
lean_inc_n(v_getEnv_2492_, 2);
lean_inc_ref(v_inst_2489_);
lean_inc_ref(v_inst_2487_);
v___f_2493_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2493_, 0, v_docs_2490_);
lean_closure_set(v___f_2493_, 1, v_inst_2487_);
lean_closure_set(v___f_2493_, 2, v_inst_2489_);
lean_closure_set(v___f_2493_, 3, v_inst_2488_);
v___f_2494_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2494_, 0, v_inst_2487_);
lean_closure_set(v___f_2494_, 1, v_inst_2489_);
lean_closure_set(v___f_2494_, 2, v_toBind_2491_);
lean_closure_set(v___f_2494_, 3, v_getEnv_2492_);
lean_closure_set(v___f_2494_, 4, v___f_2493_);
v___x_2495_ = lean_apply_4(v_toBind_2491_, lean_box(0), lean_box(0), v_getEnv_2492_, v___f_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_docs_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2497_, v_inst_2498_, v_inst_2500_, v_docs_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_docs_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_addVersoModDocStringCore(v_m_2503_, v_inst_2504_, v_inst_2505_, v_inst_2506_, v_inst_2507_, v_docs_2508_);
lean_dec(v_inst_2506_);
return v_res_2509_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2516_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
lean_ctor_set(v___x_2516_, 2, v___x_2515_);
lean_ctor_set(v___x_2516_, 3, v___x_2515_);
lean_ctor_set(v___x_2516_, 4, v___x_2515_);
lean_ctor_set(v___x_2516_, 5, v___x_2515_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2517_, lean_object* v_docs_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Name_isAnonymous(v_declName_2517_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v_env_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_st_ref_get(v___y_2524_);
v_env_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_env_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2570_, v_declName_2517_);
lean_dec_ref(v_env_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
v___y_2527_ = v___y_2522_;
v___y_2528_ = v___y_2524_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2586_; 
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2571_, 0);
lean_dec(v_unused_2587_);
v___x_2573_ = v___x_2571_;
v_isShared_2574_ = v_isSharedCheck_2586_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v___x_2571_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2586_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
if (v___x_2568_ == 0)
{
lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec_ref(v_docs_2518_);
v___x_2575_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2576_ = 1;
v___x_2577_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2517_, v___x_2576_);
v___x_2578_ = lean_string_append(v___x_2575_, v___x_2577_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2580_ = lean_string_append(v___x_2578_, v___x_2579_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 3);
lean_ctor_set(v___x_2573_, 0, v___x_2580_);
v___x_2582_ = v___x_2573_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = l_Lean_MessageData_ofFormat(v___x_2582_);
v___x_2584_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2583_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2584_;
}
}
else
{
lean_del_object(v___x_2573_);
v___y_2527_ = v___y_2522_;
v___y_2528_ = v___y_2524_;
goto v___jp_2526_;
}
}
}
}
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec_ref(v_docs_2518_);
lean_dec(v_declName_2517_);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
v___jp_2526_:
{
lean_object* v___x_2529_; lean_object* v_env_2530_; lean_object* v_nextMacroScope_2531_; lean_object* v_ngen_2532_; lean_object* v_auxDeclNGen_2533_; lean_object* v_traceState_2534_; lean_object* v_messages_2535_; lean_object* v_infoState_2536_; lean_object* v_snapshotTasks_2537_; lean_object* v_newDecls_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2566_; 
v___x_2529_ = lean_st_ref_take(v___y_2528_);
v_env_2530_ = lean_ctor_get(v___x_2529_, 0);
v_nextMacroScope_2531_ = lean_ctor_get(v___x_2529_, 1);
v_ngen_2532_ = lean_ctor_get(v___x_2529_, 2);
v_auxDeclNGen_2533_ = lean_ctor_get(v___x_2529_, 3);
v_traceState_2534_ = lean_ctor_get(v___x_2529_, 4);
v_messages_2535_ = lean_ctor_get(v___x_2529_, 6);
v_infoState_2536_ = lean_ctor_get(v___x_2529_, 7);
v_snapshotTasks_2537_ = lean_ctor_get(v___x_2529_, 8);
v_newDecls_2538_ = lean_ctor_get(v___x_2529_, 9);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2529_, 5);
lean_dec(v_unused_2567_);
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2566_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_newDecls_2538_);
lean_inc(v_snapshotTasks_2537_);
lean_inc(v_infoState_2536_);
lean_inc(v_messages_2535_);
lean_inc(v_traceState_2534_);
lean_inc(v_auxDeclNGen_2533_);
lean_inc(v_ngen_2532_);
lean_inc(v_nextMacroScope_2531_);
lean_inc(v_env_2530_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2566_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2542_ = l_Lean_versoDocStringExt;
v___x_2543_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2542_, v_env_2530_, v_declName_2517_, v_docs_2518_);
v___x_2544_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 5, v___x_2544_);
lean_ctor_set(v___x_2540_, 0, v___x_2543_);
v___x_2546_ = v___x_2540_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_nextMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_ngen_2532_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_auxDeclNGen_2533_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_traceState_2534_);
lean_ctor_set(v_reuseFailAlloc_2565_, 5, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2565_, 6, v_messages_2535_);
lean_ctor_set(v_reuseFailAlloc_2565_, 7, v_infoState_2536_);
lean_ctor_set(v_reuseFailAlloc_2565_, 8, v_snapshotTasks_2537_);
lean_ctor_set(v_reuseFailAlloc_2565_, 9, v_newDecls_2538_);
v___x_2546_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_mctx_2549_; lean_object* v_zetaDeltaFVarIds_2550_; lean_object* v_postponed_2551_; lean_object* v_diag_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2563_; 
v___x_2547_ = lean_st_ref_set(v___y_2528_, v___x_2546_);
v___x_2548_ = lean_st_ref_take(v___y_2527_);
v_mctx_2549_ = lean_ctor_get(v___x_2548_, 0);
v_zetaDeltaFVarIds_2550_ = lean_ctor_get(v___x_2548_, 2);
v_postponed_2551_ = lean_ctor_get(v___x_2548_, 3);
v_diag_2552_ = lean_ctor_get(v___x_2548_, 4);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2548_, 1);
lean_dec(v_unused_2564_);
v___x_2554_ = v___x_2548_;
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_diag_2552_);
lean_inc(v_postponed_2551_);
lean_inc(v_zetaDeltaFVarIds_2550_);
lean_inc(v_mctx_2549_);
lean_dec(v___x_2548_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2556_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 1, v___x_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_mctx_2549_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_zetaDeltaFVarIds_2550_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_postponed_2551_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_diag_2552_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = lean_st_ref_set(v___y_2527_, v___x_2558_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2590_, lean_object* v_docs_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2590_, v_docs_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2600_, lean_object* v_binders_2601_, lean_object* v_docComment_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___x_2637_; lean_object* v_env_2638_; lean_object* v___x_2639_; 
v___x_2637_ = lean_st_ref_get(v_a_2608_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
v___x_2639_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2638_, v_declName_2600_);
lean_dec_ref(v_env_2638_);
if (lean_obj_tag(v___x_2639_) == 0)
{
v___y_2611_ = v_a_2603_;
v___y_2612_ = v_a_2604_;
v___y_2613_ = v_a_2605_;
v___y_2614_ = v_a_2606_;
v___y_2615_ = v_a_2607_;
v___y_2616_ = v_a_2608_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2654_; 
lean_dec(v_docComment_2602_);
lean_dec(v_binders_2601_);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2639_, 0);
lean_dec(v_unused_2655_);
v___x_2641_ = v___x_2639_;
v_isShared_2642_ = v_isSharedCheck_2654_;
goto v_resetjp_2640_;
}
else
{
lean_dec(v___x_2639_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2654_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2643_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2644_ = 1;
v___x_2645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2600_, v___x_2644_);
v___x_2646_ = lean_string_append(v___x_2643_, v___x_2645_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2648_ = lean_string_append(v___x_2646_, v___x_2647_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 3);
lean_ctor_set(v___x_2641_, 0, v___x_2648_);
v___x_2650_ = v___x_2641_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = l_Lean_MessageData_ofFormat(v___x_2650_);
v___x_2652_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2651_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
return v___x_2652_;
}
}
}
v___jp_2610_:
{
lean_object* v___x_2617_; 
lean_inc(v_declName_2600_);
v___x_2617_ = l_Lean_versoDocString(v_declName_2600_, v_binders_2601_, v_docComment_2602_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2628_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2617_);
v_fst_2619_ = lean_ctor_get(v_a_2618_, 0);
v_snd_2620_ = lean_ctor_get(v_a_2618_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2618_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2622_ = v_a_2618_;
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_snd_2620_);
lean_inc(v_fst_2619_);
lean_dec(v_a_2618_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_fst_2619_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_snd_2620_);
v___x_2625_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2600_, v___x_2625_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_declName_2600_);
v_a_2629_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2617_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2617_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2656_, lean_object* v_binders_2657_, lean_object* v_docComment_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_addVersoDocString(v_declName_2656_, v_binders_2657_, v_docComment_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2667_, lean_object* v_docComment_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___x_2703_; lean_object* v_env_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_st_ref_get(v_a_2674_);
v_env_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc_ref(v_env_2704_);
lean_dec(v___x_2703_);
v___x_2705_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2704_, v_declName_2667_);
lean_dec_ref(v_env_2704_);
if (lean_obj_tag(v___x_2705_) == 0)
{
v___y_2677_ = v_a_2669_;
v___y_2678_ = v_a_2670_;
v___y_2679_ = v_a_2671_;
v___y_2680_ = v_a_2672_;
v___y_2681_ = v_a_2673_;
v___y_2682_ = v_a_2674_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_docComment_2668_);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2705_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; 
v_unused_2721_ = lean_ctor_get(v___x_2705_, 0);
lean_dec(v_unused_2721_);
v___x_2707_ = v___x_2705_;
v_isShared_2708_ = v_isSharedCheck_2720_;
goto v_resetjp_2706_;
}
else
{
lean_dec(v___x_2705_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2720_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2709_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2710_ = 1;
v___x_2711_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2667_, v___x_2710_);
v___x_2712_ = lean_string_append(v___x_2709_, v___x_2711_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2714_ = lean_string_append(v___x_2712_, v___x_2713_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 3);
lean_ctor_set(v___x_2707_, 0, v___x_2714_);
v___x_2716_ = v___x_2707_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = l_Lean_MessageData_ofFormat(v___x_2716_);
v___x_2718_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2717_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
return v___x_2718_;
}
}
}
v___jp_2676_:
{
lean_object* v___x_2683_; 
lean_inc(v_declName_2667_);
v___x_2683_ = l_Lean_versoDocStringFromString(v_declName_2667_, v_docComment_2668_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
v_fst_2685_ = lean_ctor_get(v_a_2684_, 0);
v_snd_2686_ = lean_ctor_get(v_a_2684_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2688_ = v_a_2684_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_snd_2686_);
lean_inc(v_fst_2685_);
lean_dec(v_a_2684_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_fst_2685_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v_snd_2686_);
v___x_2691_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2667_, v___x_2691_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_declName_2667_);
v_a_2695_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2683_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2683_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2722_, lean_object* v_docComment_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_addVersoDocStringFromString(v_declName_2722_, v_docComment_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2732_, lean_object* v_msgData_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
uint8_t v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; 
v___x_2739_ = 2;
v___x_2740_ = 0;
v___x_2741_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2732_, v_msgData_2733_, v___x_2739_, v___x_2740_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2742_, lean_object* v_msgData_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2742_, v_msgData_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v_ref_2742_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2750_, lean_object* v_str_2751_, lean_object* v_as_2752_, size_t v_sz_2753_, size_t v_i_2754_, lean_object* v_b_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_a_2764_; uint8_t v___x_2768_; 
v___x_2768_ = lean_usize_dec_lt(v_i_2754_, v_sz_2753_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_b_2755_);
return v___x_2769_;
}
else
{
lean_object* v_a_2770_; lean_object* v_fst_2771_; lean_object* v_snd_2772_; lean_object* v_start_2773_; lean_object* v_stop_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2794_; 
v_a_2770_ = lean_array_uget_borrowed(v_as_2752_, v_i_2754_);
v_fst_2771_ = lean_ctor_get(v_a_2770_, 0);
lean_inc(v_fst_2771_);
v_snd_2772_ = lean_ctor_get(v_a_2770_, 1);
v_start_2773_ = lean_ctor_get(v_fst_2771_, 0);
v_stop_2774_ = lean_ctor_get(v_fst_2771_, 1);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_fst_2771_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2776_ = v_fst_2771_;
v_isShared_2777_ = v_isSharedCheck_2794_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_stop_2774_);
lean_inc(v_start_2773_);
lean_dec(v_fst_2771_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2794_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_box(0);
if (lean_obj_tag(v___y_2750_) == 1)
{
lean_object* v_val_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v_val_2779_ = lean_ctor_get(v___y_2750_, 0);
v___x_2780_ = lean_nat_add(v_val_2779_, v_start_2773_);
v___x_2781_ = lean_nat_add(v_val_2779_, v_stop_2774_);
v___x_2782_ = 0;
v___x_2783_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2783_, 0, v___x_2780_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
lean_ctor_set_uint8(v___x_2783_, sizeof(void*)*2, v___x_2782_);
v___x_2784_ = lean_string_utf8_extract(v_str_2751_, v_start_2773_, v_stop_2774_);
lean_dec(v_stop_2774_);
lean_dec(v_start_2773_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 2);
lean_ctor_set(v___x_2776_, 1, v___x_2784_);
lean_ctor_set(v___x_2776_, 0, v___x_2783_);
v___x_2786_ = v___x_2776_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_inc(v_snd_2772_);
v___x_2787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_snd_2772_);
v___x_2788_ = l_Lean_MessageData_ofFormat(v___x_2787_);
v___x_2789_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2786_, v___x_2788_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec_ref(v___x_2786_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref(v___x_2789_);
v_a_2764_ = v___x_2778_;
goto v___jp_2763_;
}
else
{
return v___x_2789_;
}
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_del_object(v___x_2776_);
lean_dec(v_stop_2774_);
lean_dec(v_start_2773_);
lean_inc(v_snd_2772_);
v___x_2791_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_snd_2772_);
v___x_2792_ = l_Lean_MessageData_ofFormat(v___x_2791_);
v___x_2793_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2792_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref(v___x_2793_);
v_a_2764_ = v___x_2778_;
goto v___jp_2763_;
}
else
{
return v___x_2793_;
}
}
}
}
v___jp_2763_:
{
size_t v___x_2765_; size_t v___x_2766_; 
v___x_2765_ = ((size_t)1ULL);
v___x_2766_ = lean_usize_add(v_i_2754_, v___x_2765_);
v_i_2754_ = v___x_2766_;
v_b_2755_ = v_a_2764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2795_, lean_object* v_str_2796_, lean_object* v_as_2797_, lean_object* v_sz_2798_, lean_object* v_i_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
size_t v_sz_boxed_2808_; size_t v_i_boxed_2809_; lean_object* v_res_2810_; 
v_sz_boxed_2808_ = lean_unbox_usize(v_sz_2798_);
lean_dec(v_sz_2798_);
v_i_boxed_2809_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_res_2810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2795_, v_str_2796_, v_as_2797_, v_sz_boxed_2808_, v_i_boxed_2809_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_as_2797_);
lean_dec_ref(v_str_2796_);
lean_dec(v___y_2795_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_str_2819_; lean_object* v___y_2821_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_str_2819_ = l_Lean_TSyntax_getDocString(v_docstring_2811_);
v___x_2836_ = lean_unsigned_to_nat(1u);
v___x_2837_ = l_Lean_Syntax_getArg(v_docstring_2811_, v___x_2836_);
v___x_2838_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2837_);
lean_dec(v___x_2837_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_box(0);
v___y_2821_ = v___x_2839_;
goto v___jp_2820_;
}
else
{
lean_object* v_val_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v_val_2840_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_val_2840_);
lean_dec_ref(v___x_2838_);
v___x_2841_ = 0;
v___x_2842_ = l_Lean_SourceInfo_getPos_x3f(v_val_2840_, v___x_2841_);
lean_dec(v_val_2840_);
v___y_2821_ = v___x_2842_;
goto v___jp_2820_;
}
v___jp_2820_:
{
lean_object* v___x_2822_; lean_object* v_fst_2823_; lean_object* v___x_2824_; size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
lean_inc_ref(v_str_2819_);
v___x_2822_ = l_Lean_rewriteManualLinksCore(v_str_2819_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_fst_2823_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = lean_box(0);
v_sz_2825_ = lean_array_size(v_fst_2823_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2821_, v_str_2819_, v_fst_2823_, v_sz_2825_, v___x_2826_, v___x_2824_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec(v_fst_2823_);
lean_dec_ref(v_str_2819_);
lean_dec(v___y_2821_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2835_);
v___x_2829_ = v___x_2827_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v___x_2827_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2824_);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2824_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
else
{
return v___x_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_docstring_2843_);
return v_res_2851_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_val_2870_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_unsigned_to_nat(1u);
v___x_2878_ = l_Lean_Syntax_getArg(v_stx_2855_, v___x_2877_);
switch(lean_obj_tag(v___x_2878_))
{
case 2:
{
lean_object* v_val_2879_; 
lean_dec(v_stx_2855_);
v_val_2879_ = lean_ctor_get(v___x_2878_, 1);
lean_inc_ref(v_val_2879_);
lean_dec_ref(v___x_2878_);
v_val_2870_ = v_val_2879_;
goto v___jp_2869_;
}
case 1:
{
lean_object* v_kind_2880_; 
v_kind_2880_ = lean_ctor_get(v___x_2878_, 1);
lean_inc(v_kind_2880_);
if (lean_obj_tag(v_kind_2880_) == 1)
{
lean_object* v_pre_2881_; 
v_pre_2881_ = lean_ctor_get(v_kind_2880_, 0);
lean_inc(v_pre_2881_);
if (lean_obj_tag(v_pre_2881_) == 1)
{
lean_object* v_pre_2882_; 
v_pre_2882_ = lean_ctor_get(v_pre_2881_, 0);
lean_inc(v_pre_2882_);
if (lean_obj_tag(v_pre_2882_) == 1)
{
lean_object* v_pre_2883_; 
v_pre_2883_ = lean_ctor_get(v_pre_2882_, 0);
lean_inc(v_pre_2883_);
if (lean_obj_tag(v_pre_2883_) == 1)
{
lean_object* v_pre_2884_; 
v_pre_2884_ = lean_ctor_get(v_pre_2883_, 0);
if (lean_obj_tag(v_pre_2884_) == 0)
{
lean_object* v_str_2885_; lean_object* v_str_2886_; lean_object* v_str_2887_; lean_object* v_str_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_str_2885_ = lean_ctor_get(v_kind_2880_, 1);
lean_inc_ref(v_str_2885_);
lean_dec_ref(v_kind_2880_);
v_str_2886_ = lean_ctor_get(v_pre_2881_, 1);
lean_inc_ref(v_str_2886_);
lean_dec_ref(v_pre_2881_);
v_str_2887_ = lean_ctor_get(v_pre_2882_, 1);
lean_inc_ref(v_str_2887_);
lean_dec_ref(v_pre_2882_);
v_str_2888_ = lean_ctor_get(v_pre_2883_, 1);
lean_inc_ref(v_str_2888_);
lean_dec_ref(v_pre_2883_);
v___x_2889_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2890_ = lean_string_dec_eq(v_str_2888_, v___x_2889_);
lean_dec_ref(v_str_2888_);
if (v___x_2890_ == 0)
{
lean_dec_ref(v_str_2887_);
lean_dec_ref(v_str_2886_);
lean_dec_ref(v_str_2885_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2892_ = lean_string_dec_eq(v_str_2887_, v___x_2891_);
lean_dec_ref(v_str_2887_);
if (v___x_2892_ == 0)
{
lean_dec_ref(v_str_2886_);
lean_dec_ref(v_str_2885_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2893_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2894_ = lean_string_dec_eq(v_str_2886_, v___x_2893_);
lean_dec_ref(v_str_2886_);
if (v___x_2894_ == 0)
{
lean_dec_ref(v_str_2885_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2896_ = lean_string_dec_eq(v_str_2885_, v___x_2895_);
lean_dec_ref(v_str_2885_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_unsigned_to_nat(0u);
v___x_2898_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2897_);
lean_dec_ref(v___x_2878_);
if (lean_obj_tag(v___x_2898_) == 2)
{
lean_object* v_val_2899_; 
lean_dec(v_stx_2855_);
v_val_2899_ = lean_ctor_get(v___x_2898_, 1);
lean_inc_ref(v_val_2899_);
lean_dec_ref(v___x_2898_);
v_val_2870_ = v_val_2899_;
goto v___jp_2869_;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
lean_dec(v___x_2898_);
v___x_2900_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2855_);
v___x_2901_ = l_Lean_MessageData_ofSyntax(v_stx_2855_);
v___x_2902_ = l_Lean_indentD(v___x_2901_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2900_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2855_, v___x_2903_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v_stx_2855_);
return v___x_2904_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2883_);
lean_dec_ref(v_pre_2882_);
lean_dec_ref(v_pre_2881_);
lean_dec_ref(v_kind_2880_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
}
else
{
lean_dec_ref(v_pre_2882_);
lean_dec(v_pre_2883_);
lean_dec_ref(v_pre_2881_);
lean_dec_ref(v_kind_2880_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
}
else
{
lean_dec(v_pre_2882_);
lean_dec_ref(v_pre_2881_);
lean_dec_ref(v_kind_2880_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
}
else
{
lean_dec(v_pre_2881_);
lean_dec_ref(v_kind_2880_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
}
else
{
lean_dec(v_kind_2880_);
lean_dec_ref(v___x_2878_);
goto v___jp_2863_;
}
}
default: 
{
lean_dec(v___x_2878_);
goto v___jp_2863_;
}
}
v___jp_2863_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2864_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2855_);
v___x_2865_ = l_Lean_MessageData_ofSyntax(v_stx_2855_);
v___x_2866_ = l_Lean_indentD(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2864_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2855_, v___x_2867_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v_stx_2855_);
return v___x_2868_;
}
v___jp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = lean_string_utf8_byte_size(v_val_2870_);
v___x_2873_ = lean_unsigned_to_nat(2u);
v___x_2874_ = lean_nat_sub(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_string_utf8_extract(v_val_2870_, v___x_2871_, v___x_2874_);
lean_dec(v___x_2874_);
lean_dec_ref(v_val_2870_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2914_, lean_object* v_docComment_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; uint8_t v___x_2987_; 
v___x_2987_ = l_Lean_Name_isAnonymous(v_declName_2914_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2988_; lean_object* v_env_2989_; lean_object* v___x_2990_; 
v___x_2988_ = lean_st_ref_get(v___y_2921_);
v_env_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc_ref(v_env_2989_);
lean_dec(v___x_2988_);
v___x_2990_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2989_, v_declName_2914_);
lean_dec_ref(v_env_2989_);
if (lean_obj_tag(v___x_2990_) == 0)
{
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
v___y_2926_ = v___y_2918_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
goto v___jp_2923_;
}
else
{
lean_dec_ref(v___x_2990_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v_docComment_2915_);
v___x_2991_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2992_ = l_Lean_MessageData_ofConstName(v_declName_2914_, v___x_2987_);
v___x_2993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
v___x_2996_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2995_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
return v___x_2996_;
}
else
{
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
v___y_2926_ = v___y_2918_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
goto v___jp_2923_;
}
}
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_docComment_2915_);
lean_dec(v_declName_2914_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
return v___x_2998_;
}
v___jp_2923_:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2915_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v___x_2931_; 
lean_dec_ref(v___x_2930_);
v___x_2931_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2915_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2978_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2978_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2978_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v_env_2937_; lean_object* v_nextMacroScope_2938_; lean_object* v_ngen_2939_; lean_object* v_auxDeclNGen_2940_; lean_object* v_traceState_2941_; lean_object* v_messages_2942_; lean_object* v_infoState_2943_; lean_object* v_snapshotTasks_2944_; lean_object* v_newDecls_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2976_; 
v___x_2936_ = lean_st_ref_take(v___y_2929_);
v_env_2937_ = lean_ctor_get(v___x_2936_, 0);
v_nextMacroScope_2938_ = lean_ctor_get(v___x_2936_, 1);
v_ngen_2939_ = lean_ctor_get(v___x_2936_, 2);
v_auxDeclNGen_2940_ = lean_ctor_get(v___x_2936_, 3);
v_traceState_2941_ = lean_ctor_get(v___x_2936_, 4);
v_messages_2942_ = lean_ctor_get(v___x_2936_, 6);
v_infoState_2943_ = lean_ctor_get(v___x_2936_, 7);
v_snapshotTasks_2944_ = lean_ctor_get(v___x_2936_, 8);
v_newDecls_2945_ = lean_ctor_get(v___x_2936_, 9);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v___x_2936_, 5);
lean_dec(v_unused_2977_);
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_newDecls_2945_);
lean_inc(v_snapshotTasks_2944_);
lean_inc(v_infoState_2943_);
lean_inc(v_messages_2942_);
lean_inc(v_traceState_2941_);
lean_inc(v_auxDeclNGen_2940_);
lean_inc(v_ngen_2939_);
lean_inc(v_nextMacroScope_2938_);
lean_inc(v_env_2937_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2976_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2949_ = l_Lean_docStringExt;
v___x_2950_ = l_String_removeLeadingSpaces(v_a_2932_);
v___x_2951_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2949_, v_env_2937_, v_declName_2914_, v___x_2950_);
v___x_2952_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 5, v___x_2952_);
lean_ctor_set(v___x_2947_, 0, v___x_2951_);
v___x_2954_ = v___x_2947_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_nextMacroScope_2938_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_ngen_2939_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_auxDeclNGen_2940_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_traceState_2941_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2975_, 6, v_messages_2942_);
lean_ctor_set(v_reuseFailAlloc_2975_, 7, v_infoState_2943_);
lean_ctor_set(v_reuseFailAlloc_2975_, 8, v_snapshotTasks_2944_);
lean_ctor_set(v_reuseFailAlloc_2975_, 9, v_newDecls_2945_);
v___x_2954_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_mctx_2957_; lean_object* v_zetaDeltaFVarIds_2958_; lean_object* v_postponed_2959_; lean_object* v_diag_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2973_; 
v___x_2955_ = lean_st_ref_set(v___y_2929_, v___x_2954_);
v___x_2956_ = lean_st_ref_take(v___y_2927_);
v_mctx_2957_ = lean_ctor_get(v___x_2956_, 0);
v_zetaDeltaFVarIds_2958_ = lean_ctor_get(v___x_2956_, 2);
v_postponed_2959_ = lean_ctor_get(v___x_2956_, 3);
v_diag_2960_ = lean_ctor_get(v___x_2956_, 4);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v___x_2956_, 1);
lean_dec(v_unused_2974_);
v___x_2962_ = v___x_2956_;
v_isShared_2963_ = v_isSharedCheck_2973_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_diag_2960_);
lean_inc(v_postponed_2959_);
lean_inc(v_zetaDeltaFVarIds_2958_);
lean_inc(v_mctx_2957_);
lean_dec(v___x_2956_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2973_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2964_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 1, v___x_2964_);
v___x_2966_ = v___x_2962_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_mctx_2957_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_zetaDeltaFVarIds_2958_);
lean_ctor_set(v_reuseFailAlloc_2972_, 3, v_postponed_2959_);
lean_ctor_set(v_reuseFailAlloc_2972_, 4, v_diag_2960_);
v___x_2966_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2967_ = lean_st_ref_set(v___y_2927_, v___x_2966_);
v___x_2968_ = lean_box(0);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2968_);
v___x_2970_ = v___x_2934_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_declName_2914_);
v_a_2979_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2931_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2931_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_dec(v_docComment_2915_);
lean_dec(v_declName_2914_);
return v___x_2930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2999_, lean_object* v_docComment_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2999_, v_docComment_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3009_, lean_object* v_declName_3010_, lean_object* v_binders_3011_, lean_object* v_docComment_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
if (v_isVerso_3009_ == 0)
{
lean_object* v___x_3020_; 
lean_dec(v_binders_3011_);
v___x_3020_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3010_, v_docComment_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_addVersoDocString(v_declName_3010_, v_binders_3011_, v_docComment_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3022_, lean_object* v_declName_3023_, lean_object* v_binders_3024_, lean_object* v_docComment_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
uint8_t v_isVerso_boxed_3033_; lean_object* v_res_3034_; 
v_isVerso_boxed_3033_ = lean_unbox(v_isVerso_3022_);
v_res_3034_ = l_Lean_addDocStringOf(v_isVerso_boxed_3033_, v_declName_3023_, v_binders_3024_, v_docComment_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
return v_res_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3035_, lean_object* v_msgData_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3035_, v_msgData_3036_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3045_, lean_object* v_msgData_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3045_, v_msgData_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v_ref_3045_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3055_, lean_object* v_t_3056_){
_start:
{
if (lean_obj_tag(v_t_3056_) == 0)
{
lean_object* v_k_3057_; lean_object* v_v_3058_; lean_object* v_l_3059_; lean_object* v_r_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3714_; 
v_k_3057_ = lean_ctor_get(v_t_3056_, 1);
v_v_3058_ = lean_ctor_get(v_t_3056_, 2);
v_l_3059_ = lean_ctor_get(v_t_3056_, 3);
v_r_3060_ = lean_ctor_get(v_t_3056_, 4);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_t_3056_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; 
v_unused_3715_ = lean_ctor_get(v_t_3056_, 0);
lean_dec(v_unused_3715_);
v___x_3062_ = v_t_3056_;
v_isShared_3063_ = v_isSharedCheck_3714_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_r_3060_);
lean_inc(v_l_3059_);
lean_inc(v_v_3058_);
lean_inc(v_k_3057_);
lean_dec(v_t_3056_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3714_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint8_t v___x_3064_; 
v___x_3064_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3055_, v_k_3057_);
switch(v___x_3064_)
{
case 0:
{
lean_object* v_impl_3065_; lean_object* v___x_3066_; 
v_impl_3065_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3055_, v_l_3059_);
v___x_3066_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3065_) == 0)
{
if (lean_obj_tag(v_r_3060_) == 0)
{
lean_object* v_size_3067_; lean_object* v_size_3068_; lean_object* v_k_3069_; lean_object* v_v_3070_; lean_object* v_l_3071_; lean_object* v_r_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_size_3067_ = lean_ctor_get(v_impl_3065_, 0);
lean_inc(v_size_3067_);
v_size_3068_ = lean_ctor_get(v_r_3060_, 0);
v_k_3069_ = lean_ctor_get(v_r_3060_, 1);
v_v_3070_ = lean_ctor_get(v_r_3060_, 2);
v_l_3071_ = lean_ctor_get(v_r_3060_, 3);
lean_inc(v_l_3071_);
v_r_3072_ = lean_ctor_get(v_r_3060_, 4);
v___x_3073_ = lean_unsigned_to_nat(3u);
v___x_3074_ = lean_nat_mul(v___x_3073_, v_size_3067_);
v___x_3075_ = lean_nat_dec_lt(v___x_3074_, v_size_3068_);
lean_dec(v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
lean_dec(v_l_3071_);
v___x_3076_ = lean_nat_add(v___x_3066_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3077_ = lean_nat_add(v___x_3076_, v_size_3068_);
lean_dec(v___x_3076_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 3, v_impl_3065_);
lean_ctor_set(v___x_3062_, 0, v___x_3077_);
v___x_3079_ = v___x_3062_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3080_, 3, v_impl_3065_);
lean_ctor_set(v_reuseFailAlloc_3080_, 4, v_r_3060_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
else
{
lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3144_; 
lean_inc(v_r_3072_);
lean_inc(v_v_3070_);
lean_inc(v_k_3069_);
lean_inc(v_size_3068_);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; 
v_unused_3145_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3145_);
v_unused_3146_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_r_3060_, 2);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_r_3060_, 1);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3149_);
v___x_3082_ = v_r_3060_;
v_isShared_3083_ = v_isSharedCheck_3144_;
goto v_resetjp_3081_;
}
else
{
lean_dec(v_r_3060_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3144_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_size_3084_; lean_object* v_k_3085_; lean_object* v_v_3086_; lean_object* v_l_3087_; lean_object* v_r_3088_; lean_object* v_size_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; uint8_t v___x_3092_; 
v_size_3084_ = lean_ctor_get(v_l_3071_, 0);
v_k_3085_ = lean_ctor_get(v_l_3071_, 1);
v_v_3086_ = lean_ctor_get(v_l_3071_, 2);
v_l_3087_ = lean_ctor_get(v_l_3071_, 3);
v_r_3088_ = lean_ctor_get(v_l_3071_, 4);
v_size_3089_ = lean_ctor_get(v_r_3072_, 0);
v___x_3090_ = lean_unsigned_to_nat(2u);
v___x_3091_ = lean_nat_mul(v___x_3090_, v_size_3089_);
v___x_3092_ = lean_nat_dec_lt(v_size_3084_, v___x_3091_);
lean_dec(v___x_3091_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3120_; 
lean_inc(v_r_3088_);
lean_inc(v_l_3087_);
lean_inc(v_v_3086_);
lean_inc(v_k_3085_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_l_3071_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; 
v_unused_3121_ = lean_ctor_get(v_l_3071_, 4);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_l_3071_, 3);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_l_3071_, 2);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_l_3071_, 1);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_l_3071_, 0);
lean_dec(v_unused_3125_);
v___x_3094_ = v_l_3071_;
v_isShared_3095_ = v_isSharedCheck_3120_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v_l_3071_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3120_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3110_; 
v___x_3096_ = lean_nat_add(v___x_3066_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3097_ = lean_nat_add(v___x_3096_, v_size_3068_);
lean_dec(v_size_3068_);
if (lean_obj_tag(v_l_3087_) == 0)
{
lean_object* v_size_3118_; 
v_size_3118_ = lean_ctor_get(v_l_3087_, 0);
lean_inc(v_size_3118_);
v___y_3110_ = v_size_3118_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_unsigned_to_nat(0u);
v___y_3110_ = v___x_3119_;
goto v___jp_3109_;
}
v___jp_3098_:
{
lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3102_ = lean_nat_add(v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec(v___y_3100_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_r_3072_);
lean_ctor_set(v___x_3094_, 3, v_r_3088_);
lean_ctor_set(v___x_3094_, 2, v_v_3070_);
lean_ctor_set(v___x_3094_, 1, v_k_3069_);
lean_ctor_set(v___x_3094_, 0, v___x_3102_);
v___x_3104_ = v___x_3094_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_k_3069_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_v_3070_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_r_3088_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_r_3072_);
v___x_3104_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3106_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 4, v___x_3104_);
lean_ctor_set(v___x_3082_, 3, v___y_3099_);
lean_ctor_set(v___x_3082_, 2, v_v_3086_);
lean_ctor_set(v___x_3082_, 1, v_k_3085_);
lean_ctor_set(v___x_3082_, 0, v___x_3097_);
v___x_3106_ = v___x_3082_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_k_3085_);
lean_ctor_set(v_reuseFailAlloc_3107_, 2, v_v_3086_);
lean_ctor_set(v_reuseFailAlloc_3107_, 3, v___y_3099_);
lean_ctor_set(v_reuseFailAlloc_3107_, 4, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
v___jp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_nat_add(v___x_3096_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec(v___x_3096_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_l_3087_);
lean_ctor_set(v___x_3062_, 3, v_impl_3065_);
lean_ctor_set(v___x_3062_, 0, v___x_3111_);
v___x_3113_ = v___x_3062_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_impl_3065_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v_l_3087_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_nat_add(v___x_3066_, v_size_3089_);
if (lean_obj_tag(v_r_3088_) == 0)
{
lean_object* v_size_3115_; 
v_size_3115_ = lean_ctor_get(v_r_3088_, 0);
lean_inc(v_size_3115_);
v___y_3099_ = v___x_3113_;
v___y_3100_ = v___x_3114_;
v___y_3101_ = v_size_3115_;
goto v___jp_3098_;
}
else
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_unsigned_to_nat(0u);
v___y_3099_ = v___x_3113_;
v___y_3100_ = v___x_3114_;
v___y_3101_ = v___x_3116_;
goto v___jp_3098_;
}
}
}
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3130_; 
lean_del_object(v___x_3062_);
v___x_3126_ = lean_nat_add(v___x_3066_, v_size_3067_);
lean_dec(v_size_3067_);
v___x_3127_ = lean_nat_add(v___x_3126_, v_size_3068_);
lean_dec(v_size_3068_);
v___x_3128_ = lean_nat_add(v___x_3126_, v_size_3084_);
lean_dec(v___x_3126_);
lean_inc_ref(v_impl_3065_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 4, v_l_3071_);
lean_ctor_set(v___x_3082_, 3, v_impl_3065_);
lean_ctor_set(v___x_3082_, 2, v_v_3058_);
lean_ctor_set(v___x_3082_, 1, v_k_3057_);
lean_ctor_set(v___x_3082_, 0, v___x_3128_);
v___x_3130_ = v___x_3082_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_impl_3065_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_l_3071_);
v___x_3130_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
v_isSharedCheck_3137_ = !lean_is_exclusive(v_impl_3065_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; 
v_unused_3138_ = lean_ctor_get(v_impl_3065_, 4);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_impl_3065_, 3);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_impl_3065_, 2);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_impl_3065_, 1);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_impl_3065_, 0);
lean_dec(v_unused_3142_);
v___x_3132_ = v_impl_3065_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_dec(v_impl_3065_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 4, v_r_3072_);
lean_ctor_set(v___x_3132_, 3, v___x_3130_);
lean_ctor_set(v___x_3132_, 2, v_v_3070_);
lean_ctor_set(v___x_3132_, 1, v_k_3069_);
lean_ctor_set(v___x_3132_, 0, v___x_3127_);
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_k_3069_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_v_3070_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_r_3072_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v_size_3150_ = lean_ctor_get(v_impl_3065_, 0);
lean_inc(v_size_3150_);
v___x_3151_ = lean_nat_add(v___x_3066_, v_size_3150_);
lean_dec(v_size_3150_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 3, v_impl_3065_);
lean_ctor_set(v___x_3062_, 0, v___x_3151_);
v___x_3153_ = v___x_3062_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_impl_3065_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_r_3060_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
else
{
if (lean_obj_tag(v_r_3060_) == 0)
{
lean_object* v_l_3155_; 
v_l_3155_ = lean_ctor_get(v_r_3060_, 3);
lean_inc(v_l_3155_);
if (lean_obj_tag(v_l_3155_) == 0)
{
lean_object* v_r_3156_; 
v_r_3156_ = lean_ctor_get(v_r_3060_, 4);
lean_inc(v_r_3156_);
if (lean_obj_tag(v_r_3156_) == 0)
{
lean_object* v_size_3157_; lean_object* v_k_3158_; lean_object* v_v_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3172_; 
v_size_3157_ = lean_ctor_get(v_r_3060_, 0);
v_k_3158_ = lean_ctor_get(v_r_3060_, 1);
v_v_3159_ = lean_ctor_get(v_r_3060_, 2);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; lean_object* v_unused_3174_; 
v_unused_3173_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3174_);
v___x_3161_ = v_r_3060_;
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_v_3159_);
lean_inc(v_k_3158_);
lean_inc(v_size_3157_);
lean_dec(v_r_3060_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3172_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v_size_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v_size_3163_ = lean_ctor_get(v_l_3155_, 0);
v___x_3164_ = lean_nat_add(v___x_3066_, v_size_3157_);
lean_dec(v_size_3157_);
v___x_3165_ = lean_nat_add(v___x_3066_, v_size_3163_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 4, v_l_3155_);
lean_ctor_set(v___x_3161_, 3, v_impl_3065_);
lean_ctor_set(v___x_3161_, 2, v_v_3058_);
lean_ctor_set(v___x_3161_, 1, v_k_3057_);
lean_ctor_set(v___x_3161_, 0, v___x_3165_);
v___x_3167_ = v___x_3161_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_impl_3065_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_l_3155_);
v___x_3167_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3169_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_r_3156_);
lean_ctor_set(v___x_3062_, 3, v___x_3167_);
lean_ctor_set(v___x_3062_, 2, v_v_3159_);
lean_ctor_set(v___x_3062_, 1, v_k_3158_);
lean_ctor_set(v___x_3062_, 0, v___x_3164_);
v___x_3169_ = v___x_3062_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_k_3158_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_v_3159_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_r_3156_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_k_3175_; lean_object* v_v_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3199_; 
v_k_3175_ = lean_ctor_get(v_r_3060_, 1);
v_v_3176_ = lean_ctor_get(v_r_3060_, 2);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; lean_object* v_unused_3201_; lean_object* v_unused_3202_; 
v_unused_3200_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3200_);
v_unused_3201_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3202_);
v___x_3178_ = v_r_3060_;
v_isShared_3179_ = v_isSharedCheck_3199_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_v_3176_);
lean_inc(v_k_3175_);
lean_dec(v_r_3060_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3199_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_k_3180_; lean_object* v_v_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3195_; 
v_k_3180_ = lean_ctor_get(v_l_3155_, 1);
v_v_3181_ = lean_ctor_get(v_l_3155_, 2);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_l_3155_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; lean_object* v_unused_3197_; lean_object* v_unused_3198_; 
v_unused_3196_ = lean_ctor_get(v_l_3155_, 4);
lean_dec(v_unused_3196_);
v_unused_3197_ = lean_ctor_get(v_l_3155_, 3);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v_l_3155_, 0);
lean_dec(v_unused_3198_);
v___x_3183_ = v_l_3155_;
v_isShared_3184_ = v_isSharedCheck_3195_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_v_3181_);
lean_inc(v_k_3180_);
lean_dec(v_l_3155_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3195_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_unsigned_to_nat(3u);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 4, v_r_3156_);
lean_ctor_set(v___x_3183_, 3, v_r_3156_);
lean_ctor_set(v___x_3183_, 2, v_v_3058_);
lean_ctor_set(v___x_3183_, 1, v_k_3057_);
lean_ctor_set(v___x_3183_, 0, v___x_3066_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_r_3156_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v_r_3156_);
v___x_3187_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 3, v_r_3156_);
lean_ctor_set(v___x_3178_, 0, v___x_3066_);
v___x_3189_ = v___x_3178_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_k_3175_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_v_3176_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_r_3156_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_r_3156_);
v___x_3189_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3191_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3189_);
lean_ctor_set(v___x_3062_, 3, v___x_3187_);
lean_ctor_set(v___x_3062_, 2, v_v_3181_);
lean_ctor_set(v___x_3062_, 1, v_k_3180_);
lean_ctor_set(v___x_3062_, 0, v___x_3185_);
v___x_3191_ = v___x_3062_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_k_3180_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_v_3181_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3203_; 
v_r_3203_ = lean_ctor_get(v_r_3060_, 4);
lean_inc(v_r_3203_);
if (lean_obj_tag(v_r_3203_) == 0)
{
lean_object* v_k_3204_; lean_object* v_v_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3216_; 
v_k_3204_ = lean_ctor_get(v_r_3060_, 1);
v_v_3205_ = lean_ctor_get(v_r_3060_, 2);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3217_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3219_);
v___x_3207_ = v_r_3060_;
v_isShared_3208_ = v_isSharedCheck_3216_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_v_3205_);
lean_inc(v_k_3204_);
lean_dec(v_r_3060_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3216_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = lean_unsigned_to_nat(3u);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 4, v_l_3155_);
lean_ctor_set(v___x_3207_, 2, v_v_3058_);
lean_ctor_set(v___x_3207_, 1, v_k_3057_);
lean_ctor_set(v___x_3207_, 0, v___x_3066_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v_l_3155_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v_l_3155_);
v___x_3211_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_r_3203_);
lean_ctor_set(v___x_3062_, 3, v___x_3211_);
lean_ctor_set(v___x_3062_, 2, v_v_3205_);
lean_ctor_set(v___x_3062_, 1, v_k_3204_);
lean_ctor_set(v___x_3062_, 0, v___x_3209_);
v___x_3213_ = v___x_3062_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_k_3204_);
lean_ctor_set(v_reuseFailAlloc_3214_, 2, v_v_3205_);
lean_ctor_set(v_reuseFailAlloc_3214_, 3, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3214_, 4, v_r_3203_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_size_3220_; lean_object* v_k_3221_; lean_object* v_v_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3233_; 
v_size_3220_ = lean_ctor_get(v_r_3060_, 0);
v_k_3221_ = lean_ctor_get(v_r_3060_, 1);
v_v_3222_ = lean_ctor_get(v_r_3060_, 2);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; lean_object* v_unused_3235_; 
v_unused_3234_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3235_);
v___x_3224_ = v_r_3060_;
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_v_3222_);
lean_inc(v_k_3221_);
lean_inc(v_size_3220_);
lean_dec(v_r_3060_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3233_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 3, v_r_3203_);
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_size_3220_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_k_3221_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_v_3222_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_r_3203_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v_r_3203_);
v___x_3227_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_unsigned_to_nat(2u);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3227_);
lean_ctor_set(v___x_3062_, 3, v_r_3203_);
lean_ctor_set(v___x_3062_, 0, v___x_3228_);
v___x_3230_ = v___x_3062_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_r_3203_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___x_3227_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
else
{
lean_object* v___x_3237_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 3, v_r_3060_);
lean_ctor_set(v___x_3062_, 0, v___x_3066_);
v___x_3237_ = v___x_3062_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3066_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_r_3060_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_r_3060_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3062_);
lean_dec(v_v_3058_);
lean_dec(v_k_3057_);
if (lean_obj_tag(v_l_3059_) == 0)
{
if (lean_obj_tag(v_r_3060_) == 0)
{
lean_object* v_size_3239_; lean_object* v_k_3240_; lean_object* v_v_3241_; lean_object* v_l_3242_; lean_object* v_r_3243_; lean_object* v_size_3244_; lean_object* v_k_3245_; lean_object* v_v_3246_; lean_object* v_l_3247_; lean_object* v_r_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_size_3239_ = lean_ctor_get(v_l_3059_, 0);
v_k_3240_ = lean_ctor_get(v_l_3059_, 1);
v_v_3241_ = lean_ctor_get(v_l_3059_, 2);
v_l_3242_ = lean_ctor_get(v_l_3059_, 3);
v_r_3243_ = lean_ctor_get(v_l_3059_, 4);
lean_inc(v_r_3243_);
v_size_3244_ = lean_ctor_get(v_r_3060_, 0);
v_k_3245_ = lean_ctor_get(v_r_3060_, 1);
v_v_3246_ = lean_ctor_get(v_r_3060_, 2);
v_l_3247_ = lean_ctor_get(v_r_3060_, 3);
lean_inc(v_l_3247_);
v_r_3248_ = lean_ctor_get(v_r_3060_, 4);
v___x_3249_ = lean_unsigned_to_nat(1u);
v___x_3250_ = lean_nat_dec_lt(v_size_3239_, v_size_3244_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3386_; 
lean_inc(v_l_3242_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; lean_object* v_unused_3390_; lean_object* v_unused_3391_; 
v_unused_3387_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_l_3059_, 2);
lean_dec(v_unused_3389_);
v_unused_3390_ = lean_ctor_get(v_l_3059_, 1);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3391_);
v___x_3252_ = v_l_3059_;
v_isShared_3253_ = v_isSharedCheck_3386_;
goto v_resetjp_3251_;
}
else
{
lean_dec(v_l_3059_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3386_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v_tree_3255_; 
v___x_3254_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3240_, v_v_3241_, v_l_3242_, v_r_3243_);
v_tree_3255_ = lean_ctor_get(v___x_3254_, 2);
lean_inc(v_tree_3255_);
if (lean_obj_tag(v_tree_3255_) == 0)
{
lean_object* v_k_3256_; lean_object* v_v_3257_; lean_object* v_size_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v_k_3256_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_k_3256_);
v_v_3257_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_v_3257_);
lean_dec_ref(v___x_3254_);
v_size_3258_ = lean_ctor_get(v_tree_3255_, 0);
v___x_3259_ = lean_unsigned_to_nat(3u);
v___x_3260_ = lean_nat_mul(v___x_3259_, v_size_3258_);
v___x_3261_ = lean_nat_dec_lt(v___x_3260_, v_size_3244_);
lean_dec(v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
lean_dec(v_l_3247_);
v___x_3262_ = lean_nat_add(v___x_3249_, v_size_3258_);
v___x_3263_ = lean_nat_add(v___x_3262_, v_size_3244_);
lean_dec(v___x_3262_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_r_3060_);
lean_ctor_set(v___x_3252_, 3, v_tree_3255_);
lean_ctor_set(v___x_3252_, 2, v_v_3257_);
lean_ctor_set(v___x_3252_, 1, v_k_3256_);
lean_ctor_set(v___x_3252_, 0, v___x_3263_);
v___x_3265_ = v___x_3252_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_k_3256_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_v_3257_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_tree_3255_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v_r_3060_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
else
{
lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3321_; 
lean_inc(v_r_3248_);
lean_inc(v_v_3246_);
lean_inc(v_k_3245_);
lean_inc(v_size_3244_);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; lean_object* v_unused_3326_; 
v_unused_3322_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_r_3060_, 2);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_r_3060_, 1);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3326_);
v___x_3268_ = v_r_3060_;
v_isShared_3269_ = v_isSharedCheck_3321_;
goto v_resetjp_3267_;
}
else
{
lean_dec(v_r_3060_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3321_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_size_3270_; lean_object* v_k_3271_; lean_object* v_v_3272_; lean_object* v_l_3273_; lean_object* v_r_3274_; lean_object* v_size_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v_size_3270_ = lean_ctor_get(v_l_3247_, 0);
v_k_3271_ = lean_ctor_get(v_l_3247_, 1);
v_v_3272_ = lean_ctor_get(v_l_3247_, 2);
v_l_3273_ = lean_ctor_get(v_l_3247_, 3);
v_r_3274_ = lean_ctor_get(v_l_3247_, 4);
v_size_3275_ = lean_ctor_get(v_r_3248_, 0);
v___x_3276_ = lean_unsigned_to_nat(2u);
v___x_3277_ = lean_nat_mul(v___x_3276_, v_size_3275_);
v___x_3278_ = lean_nat_dec_lt(v_size_3270_, v___x_3277_);
lean_dec(v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3306_; 
lean_inc(v_r_3274_);
lean_inc(v_l_3273_);
lean_inc(v_v_3272_);
lean_inc(v_k_3271_);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_l_3247_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; 
v_unused_3307_ = lean_ctor_get(v_l_3247_, 4);
lean_dec(v_unused_3307_);
v_unused_3308_ = lean_ctor_get(v_l_3247_, 3);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_l_3247_, 2);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_3247_, 1);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_3247_, 0);
lean_dec(v_unused_3311_);
v___x_3280_ = v_l_3247_;
v_isShared_3281_ = v_isSharedCheck_3306_;
goto v_resetjp_3279_;
}
else
{
lean_dec(v_l_3247_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3306_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3296_; 
v___x_3282_ = lean_nat_add(v___x_3249_, v_size_3258_);
v___x_3283_ = lean_nat_add(v___x_3282_, v_size_3244_);
lean_dec(v_size_3244_);
if (lean_obj_tag(v_l_3273_) == 0)
{
lean_object* v_size_3304_; 
v_size_3304_ = lean_ctor_get(v_l_3273_, 0);
lean_inc(v_size_3304_);
v___y_3296_ = v_size_3304_;
goto v___jp_3295_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_unsigned_to_nat(0u);
v___y_3296_ = v___x_3305_;
goto v___jp_3295_;
}
v___jp_3284_:
{
lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3288_ = lean_nat_add(v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec(v___y_3286_);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 4, v_r_3248_);
lean_ctor_set(v___x_3280_, 3, v_r_3274_);
lean_ctor_set(v___x_3280_, 2, v_v_3246_);
lean_ctor_set(v___x_3280_, 1, v_k_3245_);
lean_ctor_set(v___x_3280_, 0, v___x_3288_);
v___x_3290_ = v___x_3280_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3288_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_r_3274_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v_r_3248_);
v___x_3290_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3292_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v___x_3290_);
lean_ctor_set(v___x_3268_, 3, v___y_3285_);
lean_ctor_set(v___x_3268_, 2, v_v_3272_);
lean_ctor_set(v___x_3268_, 1, v_k_3271_);
lean_ctor_set(v___x_3268_, 0, v___x_3283_);
v___x_3292_ = v___x_3268_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v___y_3285_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
v___jp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3299_; 
v___x_3297_ = lean_nat_add(v___x_3282_, v___y_3296_);
lean_dec(v___y_3296_);
lean_dec(v___x_3282_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_l_3273_);
lean_ctor_set(v___x_3252_, 3, v_tree_3255_);
lean_ctor_set(v___x_3252_, 2, v_v_3257_);
lean_ctor_set(v___x_3252_, 1, v_k_3256_);
lean_ctor_set(v___x_3252_, 0, v___x_3297_);
v___x_3299_ = v___x_3252_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_k_3256_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_v_3257_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_tree_3255_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v_l_3273_);
v___x_3299_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_nat_add(v___x_3249_, v_size_3275_);
if (lean_obj_tag(v_r_3274_) == 0)
{
lean_object* v_size_3301_; 
v_size_3301_ = lean_ctor_get(v_r_3274_, 0);
lean_inc(v_size_3301_);
v___y_3285_ = v___x_3299_;
v___y_3286_ = v___x_3300_;
v___y_3287_ = v_size_3301_;
goto v___jp_3284_;
}
else
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_unsigned_to_nat(0u);
v___y_3285_ = v___x_3299_;
v___y_3286_ = v___x_3300_;
v___y_3287_ = v___x_3302_;
goto v___jp_3284_;
}
}
}
}
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v___x_3312_ = lean_nat_add(v___x_3249_, v_size_3258_);
v___x_3313_ = lean_nat_add(v___x_3312_, v_size_3244_);
lean_dec(v_size_3244_);
v___x_3314_ = lean_nat_add(v___x_3312_, v_size_3270_);
lean_dec(v___x_3312_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v_l_3247_);
lean_ctor_set(v___x_3268_, 3, v_tree_3255_);
lean_ctor_set(v___x_3268_, 2, v_v_3257_);
lean_ctor_set(v___x_3268_, 1, v_k_3256_);
lean_ctor_set(v___x_3268_, 0, v___x_3314_);
v___x_3316_ = v___x_3268_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_k_3256_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_v_3257_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_tree_3255_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_l_3247_);
v___x_3316_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3318_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_r_3248_);
lean_ctor_set(v___x_3252_, 3, v___x_3316_);
lean_ctor_set(v___x_3252_, 2, v_v_3246_);
lean_ctor_set(v___x_3252_, 1, v_k_3245_);
lean_ctor_set(v___x_3252_, 0, v___x_3313_);
v___x_3318_ = v___x_3252_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v_r_3248_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
else
{
lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3380_; 
lean_inc(v_r_3248_);
lean_inc(v_v_3246_);
lean_inc(v_k_3245_);
lean_inc(v_size_3244_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3381_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_r_3060_, 2);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3060_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3385_);
v___x_3328_ = v_r_3060_;
v_isShared_3329_ = v_isSharedCheck_3380_;
goto v_resetjp_3327_;
}
else
{
lean_dec(v_r_3060_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3380_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
if (lean_obj_tag(v_l_3247_) == 0)
{
if (lean_obj_tag(v_r_3248_) == 0)
{
lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_size_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v_k_3330_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_k_3330_);
v_v_3331_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_v_3331_);
lean_dec_ref(v___x_3254_);
v_size_3332_ = lean_ctor_get(v_l_3247_, 0);
v___x_3333_ = lean_nat_add(v___x_3249_, v_size_3244_);
lean_dec(v_size_3244_);
v___x_3334_ = lean_nat_add(v___x_3249_, v_size_3332_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 4, v_l_3247_);
lean_ctor_set(v___x_3328_, 3, v_tree_3255_);
lean_ctor_set(v___x_3328_, 2, v_v_3331_);
lean_ctor_set(v___x_3328_, 1, v_k_3330_);
lean_ctor_set(v___x_3328_, 0, v___x_3334_);
v___x_3336_ = v___x_3328_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_tree_3255_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_l_3247_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_r_3248_);
lean_ctor_set(v___x_3252_, 3, v___x_3336_);
lean_ctor_set(v___x_3252_, 2, v_v_3246_);
lean_ctor_set(v___x_3252_, 1, v_k_3245_);
lean_ctor_set(v___x_3252_, 0, v___x_3333_);
v___x_3338_ = v___x_3252_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_r_3248_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
else
{
lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_k_3343_; lean_object* v_v_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_size_3244_);
v_k_3341_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_k_3341_);
v_v_3342_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_v_3342_);
lean_dec_ref(v___x_3254_);
v_k_3343_ = lean_ctor_get(v_l_3247_, 1);
v_v_3344_ = lean_ctor_get(v_l_3247_, 2);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_l_3247_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; lean_object* v_unused_3360_; lean_object* v_unused_3361_; 
v_unused_3359_ = lean_ctor_get(v_l_3247_, 4);
lean_dec(v_unused_3359_);
v_unused_3360_ = lean_ctor_get(v_l_3247_, 3);
lean_dec(v_unused_3360_);
v_unused_3361_ = lean_ctor_get(v_l_3247_, 0);
lean_dec(v_unused_3361_);
v___x_3346_ = v_l_3247_;
v_isShared_3347_ = v_isSharedCheck_3358_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_v_3344_);
lean_inc(v_k_3343_);
lean_dec(v_l_3247_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3358_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = lean_unsigned_to_nat(3u);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 4, v_r_3248_);
lean_ctor_set(v___x_3346_, 3, v_r_3248_);
lean_ctor_set(v___x_3346_, 2, v_v_3342_);
lean_ctor_set(v___x_3346_, 1, v_k_3341_);
lean_ctor_set(v___x_3346_, 0, v___x_3249_);
v___x_3350_ = v___x_3346_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3357_, 1, v_k_3341_);
lean_ctor_set(v_reuseFailAlloc_3357_, 2, v_v_3342_);
lean_ctor_set(v_reuseFailAlloc_3357_, 3, v_r_3248_);
lean_ctor_set(v_reuseFailAlloc_3357_, 4, v_r_3248_);
v___x_3350_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 3, v_r_3248_);
lean_ctor_set(v___x_3328_, 0, v___x_3249_);
v___x_3352_ = v___x_3328_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v_r_3248_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v_r_3248_);
v___x_3352_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3354_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v___x_3352_);
lean_ctor_set(v___x_3252_, 3, v___x_3350_);
lean_ctor_set(v___x_3252_, 2, v_v_3344_);
lean_ctor_set(v___x_3252_, 1, v_k_3343_);
lean_ctor_set(v___x_3252_, 0, v___x_3348_);
v___x_3354_ = v___x_3252_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3343_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3344_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v___x_3352_);
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
}
else
{
if (lean_obj_tag(v_r_3248_) == 0)
{
lean_object* v_k_3362_; lean_object* v_v_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_dec(v_size_3244_);
v_k_3362_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_k_3362_);
v_v_3363_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_v_3363_);
lean_dec_ref(v___x_3254_);
v___x_3364_ = lean_unsigned_to_nat(3u);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 4, v_l_3247_);
lean_ctor_set(v___x_3328_, 2, v_v_3363_);
lean_ctor_set(v___x_3328_, 1, v_k_3362_);
lean_ctor_set(v___x_3328_, 0, v___x_3249_);
v___x_3366_ = v___x_3328_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3362_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3363_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3247_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3247_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_r_3248_);
lean_ctor_set(v___x_3252_, 3, v___x_3366_);
lean_ctor_set(v___x_3252_, 2, v_v_3246_);
lean_ctor_set(v___x_3252_, 1, v_k_3245_);
lean_ctor_set(v___x_3252_, 0, v___x_3364_);
v___x_3368_ = v___x_3252_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_r_3248_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
else
{
lean_object* v_k_3371_; lean_object* v_v_3372_; lean_object* v___x_3374_; 
v_k_3371_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_k_3371_);
v_v_3372_ = lean_ctor_get(v___x_3254_, 1);
lean_inc(v_v_3372_);
lean_dec_ref(v___x_3254_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 3, v_r_3248_);
v___x_3374_ = v___x_3328_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_size_3244_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3245_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3246_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_r_3248_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_r_3248_);
v___x_3374_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_unsigned_to_nat(2u);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v___x_3374_);
lean_ctor_set(v___x_3252_, 3, v_r_3248_);
lean_ctor_set(v___x_3252_, 2, v_v_3372_);
lean_ctor_set(v___x_3252_, 1, v_k_3371_);
lean_ctor_set(v___x_3252_, 0, v___x_3375_);
v___x_3377_ = v___x_3252_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3371_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3372_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_r_3248_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3374_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
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
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3544_; 
lean_inc(v_r_3248_);
lean_inc(v_v_3246_);
lean_inc(v_k_3245_);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_r_3060_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3545_ = lean_ctor_get(v_r_3060_, 4);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_r_3060_, 3);
lean_dec(v_unused_3546_);
v_unused_3547_ = lean_ctor_get(v_r_3060_, 2);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_r_3060_, 1);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_r_3060_, 0);
lean_dec(v_unused_3549_);
v___x_3393_ = v_r_3060_;
v_isShared_3394_ = v_isSharedCheck_3544_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v_r_3060_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3544_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v_tree_3396_; 
v___x_3395_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3245_, v_v_3246_, v_l_3247_, v_r_3248_);
v_tree_3396_ = lean_ctor_get(v___x_3395_, 2);
lean_inc(v_tree_3396_);
if (lean_obj_tag(v_tree_3396_) == 0)
{
lean_object* v_k_3397_; lean_object* v_v_3398_; lean_object* v_size_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v_k_3397_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_k_3397_);
v_v_3398_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_v_3398_);
lean_dec_ref(v___x_3395_);
v_size_3399_ = lean_ctor_get(v_tree_3396_, 0);
v___x_3400_ = lean_unsigned_to_nat(3u);
v___x_3401_ = lean_nat_mul(v___x_3400_, v_size_3399_);
v___x_3402_ = lean_nat_dec_lt(v___x_3401_, v_size_3239_);
lean_dec(v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3406_; 
lean_dec(v_r_3243_);
v___x_3403_ = lean_nat_add(v___x_3249_, v_size_3239_);
v___x_3404_ = lean_nat_add(v___x_3403_, v_size_3399_);
lean_dec(v___x_3403_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_tree_3396_);
lean_ctor_set(v___x_3393_, 3, v_l_3059_);
lean_ctor_set(v___x_3393_, 2, v_v_3398_);
lean_ctor_set(v___x_3393_, 1, v_k_3397_);
lean_ctor_set(v___x_3393_, 0, v___x_3404_);
v___x_3406_ = v___x_3393_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_k_3397_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_v_3398_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_tree_3396_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
else
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3473_; 
lean_inc(v_l_3242_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
lean_inc(v_size_3239_);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; lean_object* v_unused_3475_; lean_object* v_unused_3476_; lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3474_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3474_);
v_unused_3475_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_l_3059_, 2);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_l_3059_, 1);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3478_);
v___x_3409_ = v_l_3059_;
v_isShared_3410_ = v_isSharedCheck_3473_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v_l_3059_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3473_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_size_3411_; lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v_l_3415_; lean_object* v_r_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v_size_3411_ = lean_ctor_get(v_l_3242_, 0);
v_size_3412_ = lean_ctor_get(v_r_3243_, 0);
v_k_3413_ = lean_ctor_get(v_r_3243_, 1);
v_v_3414_ = lean_ctor_get(v_r_3243_, 2);
v_l_3415_ = lean_ctor_get(v_r_3243_, 3);
v_r_3416_ = lean_ctor_get(v_r_3243_, 4);
v___x_3417_ = lean_unsigned_to_nat(2u);
v___x_3418_ = lean_nat_mul(v___x_3417_, v_size_3411_);
v___x_3419_ = lean_nat_dec_lt(v_size_3412_, v___x_3418_);
lean_dec(v___x_3418_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3457_; 
lean_inc(v_r_3416_);
lean_inc(v_l_3415_);
lean_inc(v_v_3414_);
lean_inc(v_k_3413_);
lean_del_object(v___x_3409_);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_r_3243_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; lean_object* v_unused_3459_; lean_object* v_unused_3460_; lean_object* v_unused_3461_; lean_object* v_unused_3462_; 
v_unused_3458_ = lean_ctor_get(v_r_3243_, 4);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v_r_3243_, 3);
lean_dec(v_unused_3459_);
v_unused_3460_ = lean_ctor_get(v_r_3243_, 2);
lean_dec(v_unused_3460_);
v_unused_3461_ = lean_ctor_get(v_r_3243_, 1);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_r_3243_, 0);
lean_dec(v_unused_3462_);
v___x_3421_ = v_r_3243_;
v_isShared_3422_ = v_isSharedCheck_3457_;
goto v_resetjp_3420_;
}
else
{
lean_dec(v_r_3243_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3457_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___x_3445_; lean_object* v___y_3447_; 
v___x_3423_ = lean_nat_add(v___x_3249_, v_size_3239_);
lean_dec(v_size_3239_);
v___x_3424_ = lean_nat_add(v___x_3423_, v_size_3399_);
lean_dec(v___x_3423_);
v___x_3445_ = lean_nat_add(v___x_3249_, v_size_3411_);
if (lean_obj_tag(v_l_3415_) == 0)
{
lean_object* v_size_3455_; 
v_size_3455_ = lean_ctor_get(v_l_3415_, 0);
lean_inc(v_size_3455_);
v___y_3447_ = v_size_3455_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3456_; 
v___x_3456_ = lean_unsigned_to_nat(0u);
v___y_3447_ = v___x_3456_;
goto v___jp_3446_;
}
v___jp_3425_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_nat_add(v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec(v___y_3427_);
lean_inc_ref(v_tree_3396_);
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 4, v_tree_3396_);
lean_ctor_set(v___x_3421_, 3, v_r_3416_);
lean_ctor_set(v___x_3421_, 2, v_v_3398_);
lean_ctor_set(v___x_3421_, 1, v_k_3397_);
lean_ctor_set(v___x_3421_, 0, v___x_3429_);
v___x_3431_ = v___x_3421_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3397_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3398_);
lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_r_3416_);
lean_ctor_set(v_reuseFailAlloc_3444_, 4, v_tree_3396_);
v___x_3431_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_isSharedCheck_3438_ = !lean_is_exclusive(v_tree_3396_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; lean_object* v_unused_3440_; lean_object* v_unused_3441_; lean_object* v_unused_3442_; lean_object* v_unused_3443_; 
v_unused_3439_ = lean_ctor_get(v_tree_3396_, 4);
lean_dec(v_unused_3439_);
v_unused_3440_ = lean_ctor_get(v_tree_3396_, 3);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_tree_3396_, 2);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_tree_3396_, 1);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_tree_3396_, 0);
lean_dec(v_unused_3443_);
v___x_3433_ = v_tree_3396_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v_tree_3396_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 4, v___x_3431_);
lean_ctor_set(v___x_3433_, 3, v___y_3426_);
lean_ctor_set(v___x_3433_, 2, v_v_3414_);
lean_ctor_set(v___x_3433_, 1, v_k_3413_);
lean_ctor_set(v___x_3433_, 0, v___x_3424_);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3426_);
lean_ctor_set(v_reuseFailAlloc_3437_, 4, v___x_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
v___jp_3446_:
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
v___x_3448_ = lean_nat_add(v___x_3445_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec(v___x_3445_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_l_3415_);
lean_ctor_set(v___x_3393_, 3, v_l_3242_);
lean_ctor_set(v___x_3393_, 2, v_v_3241_);
lean_ctor_set(v___x_3393_, 1, v_k_3240_);
lean_ctor_set(v___x_3393_, 0, v___x_3448_);
v___x_3450_ = v___x_3393_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_l_3415_);
v___x_3450_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_nat_add(v___x_3249_, v_size_3399_);
if (lean_obj_tag(v_r_3416_) == 0)
{
lean_object* v_size_3452_; 
v_size_3452_ = lean_ctor_get(v_r_3416_, 0);
lean_inc(v_size_3452_);
v___y_3426_ = v___x_3450_;
v___y_3427_ = v___x_3451_;
v___y_3428_ = v_size_3452_;
goto v___jp_3425_;
}
else
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
v___y_3426_ = v___x_3450_;
v___y_3427_ = v___x_3451_;
v___y_3428_ = v___x_3453_;
goto v___jp_3425_;
}
}
}
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3463_ = lean_nat_add(v___x_3249_, v_size_3239_);
lean_dec(v_size_3239_);
v___x_3464_ = lean_nat_add(v___x_3463_, v_size_3399_);
lean_dec(v___x_3463_);
v___x_3465_ = lean_nat_add(v___x_3249_, v_size_3399_);
v___x_3466_ = lean_nat_add(v___x_3465_, v_size_3412_);
lean_dec(v___x_3465_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_tree_3396_);
lean_ctor_set(v___x_3393_, 3, v_r_3243_);
lean_ctor_set(v___x_3393_, 2, v_v_3398_);
lean_ctor_set(v___x_3393_, 1, v_k_3397_);
lean_ctor_set(v___x_3393_, 0, v___x_3466_);
v___x_3468_ = v___x_3393_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_k_3397_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_v_3398_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3472_, 4, v_tree_3396_);
v___x_3468_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 4, v___x_3468_);
lean_ctor_set(v___x_3409_, 0, v___x_3464_);
v___x_3470_ = v___x_3409_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3242_) == 0)
{
lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3502_; 
lean_inc_ref(v_l_3242_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
lean_inc(v_size_3239_);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; lean_object* v_unused_3504_; lean_object* v_unused_3505_; lean_object* v_unused_3506_; lean_object* v_unused_3507_; 
v_unused_3503_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_l_3059_, 2);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_l_3059_, 1);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3507_);
v___x_3480_ = v_l_3059_;
v_isShared_3481_ = v_isSharedCheck_3502_;
goto v_resetjp_3479_;
}
else
{
lean_dec(v_l_3059_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3502_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
if (lean_obj_tag(v_r_3243_) == 0)
{
lean_object* v_k_3482_; lean_object* v_v_3483_; lean_object* v_size_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v_k_3482_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_k_3482_);
v_v_3483_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_v_3483_);
lean_dec_ref(v___x_3395_);
v_size_3484_ = lean_ctor_get(v_r_3243_, 0);
v___x_3485_ = lean_nat_add(v___x_3249_, v_size_3239_);
lean_dec(v_size_3239_);
v___x_3486_ = lean_nat_add(v___x_3249_, v_size_3484_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_tree_3396_);
lean_ctor_set(v___x_3393_, 3, v_r_3243_);
lean_ctor_set(v___x_3393_, 2, v_v_3483_);
lean_ctor_set(v___x_3393_, 1, v_k_3482_);
lean_ctor_set(v___x_3393_, 0, v___x_3486_);
v___x_3488_ = v___x_3393_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_k_3482_);
lean_ctor_set(v_reuseFailAlloc_3492_, 2, v_v_3483_);
lean_ctor_set(v_reuseFailAlloc_3492_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3492_, 4, v_tree_3396_);
v___x_3488_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 4, v___x_3488_);
lean_ctor_set(v___x_3480_, 0, v___x_3485_);
v___x_3490_ = v___x_3480_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3491_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3491_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3491_, 4, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
else
{
lean_object* v_k_3493_; lean_object* v_v_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
lean_dec(v_size_3239_);
v_k_3493_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_k_3493_);
v_v_3494_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_v_3494_);
lean_dec_ref(v___x_3395_);
v___x_3495_ = lean_unsigned_to_nat(3u);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_r_3243_);
lean_ctor_set(v___x_3393_, 3, v_r_3243_);
lean_ctor_set(v___x_3393_, 2, v_v_3494_);
lean_ctor_set(v___x_3393_, 1, v_k_3493_);
lean_ctor_set(v___x_3393_, 0, v___x_3249_);
v___x_3497_ = v___x_3393_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3493_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3494_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3243_);
v___x_3497_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3499_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 4, v___x_3497_);
lean_ctor_set(v___x_3480_, 0, v___x_3495_);
v___x_3499_ = v___x_3480_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3495_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3243_) == 0)
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3532_; 
lean_inc(v_l_3242_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3532_ == 0)
{
lean_object* v_unused_3533_; lean_object* v_unused_3534_; lean_object* v_unused_3535_; lean_object* v_unused_3536_; lean_object* v_unused_3537_; 
v_unused_3533_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3533_);
v_unused_3534_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3534_);
v_unused_3535_ = lean_ctor_get(v_l_3059_, 2);
lean_dec(v_unused_3535_);
v_unused_3536_ = lean_ctor_get(v_l_3059_, 1);
lean_dec(v_unused_3536_);
v_unused_3537_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3537_);
v___x_3509_ = v_l_3059_;
v_isShared_3510_ = v_isSharedCheck_3532_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v_l_3059_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3532_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v_k_3513_; lean_object* v_v_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3528_; 
v_k_3511_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_k_3511_);
v_v_3512_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_v_3512_);
lean_dec_ref(v___x_3395_);
v_k_3513_ = lean_ctor_get(v_r_3243_, 1);
v_v_3514_ = lean_ctor_get(v_r_3243_, 2);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_r_3243_);
if (v_isSharedCheck_3528_ == 0)
{
lean_object* v_unused_3529_; lean_object* v_unused_3530_; lean_object* v_unused_3531_; 
v_unused_3529_ = lean_ctor_get(v_r_3243_, 4);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_r_3243_, 3);
lean_dec(v_unused_3530_);
v_unused_3531_ = lean_ctor_get(v_r_3243_, 0);
lean_dec(v_unused_3531_);
v___x_3516_ = v_r_3243_;
v_isShared_3517_ = v_isSharedCheck_3528_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_v_3514_);
lean_inc(v_k_3513_);
lean_dec(v_r_3243_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3528_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = lean_unsigned_to_nat(3u);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 4, v_l_3242_);
lean_ctor_set(v___x_3516_, 3, v_l_3242_);
lean_ctor_set(v___x_3516_, 2, v_v_3241_);
lean_ctor_set(v___x_3516_, 1, v_k_3240_);
lean_ctor_set(v___x_3516_, 0, v___x_3249_);
v___x_3520_ = v___x_3516_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_l_3242_);
v___x_3520_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_l_3242_);
lean_ctor_set(v___x_3393_, 3, v_l_3242_);
lean_ctor_set(v___x_3393_, 2, v_v_3512_);
lean_ctor_set(v___x_3393_, 1, v_k_3511_);
lean_ctor_set(v___x_3393_, 0, v___x_3249_);
v___x_3522_ = v___x_3393_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v_l_3242_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3524_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v___x_3522_);
lean_ctor_set(v___x_3509_, 3, v___x_3520_);
lean_ctor_set(v___x_3509_, 2, v_v_3514_);
lean_ctor_set(v___x_3509_, 1, v_k_3513_);
lean_ctor_set(v___x_3509_, 0, v___x_3518_);
v___x_3524_ = v___x_3509_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
}
}
else
{
lean_object* v_k_3538_; lean_object* v_v_3539_; lean_object* v___x_3540_; lean_object* v___x_3542_; 
v_k_3538_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_k_3538_);
v_v_3539_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_v_3539_);
lean_dec_ref(v___x_3395_);
v___x_3540_ = lean_unsigned_to_nat(2u);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v_r_3243_);
lean_ctor_set(v___x_3393_, 3, v_l_3059_);
lean_ctor_set(v___x_3393_, 2, v_v_3539_);
lean_ctor_set(v___x_3393_, 1, v_k_3538_);
lean_ctor_set(v___x_3393_, 0, v___x_3540_);
v___x_3542_ = v___x_3393_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_k_3538_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_v_3539_);
lean_ctor_set(v_reuseFailAlloc_3543_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3543_, 4, v_r_3243_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
}
}
else
{
return v_l_3059_;
}
}
else
{
return v_r_3060_;
}
}
default: 
{
lean_object* v_impl_3550_; lean_object* v___x_3551_; 
v_impl_3550_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3055_, v_r_3060_);
v___x_3551_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3550_) == 0)
{
if (lean_obj_tag(v_l_3059_) == 0)
{
lean_object* v_size_3552_; lean_object* v_size_3553_; lean_object* v_k_3554_; lean_object* v_v_3555_; lean_object* v_l_3556_; lean_object* v_r_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v_size_3552_ = lean_ctor_get(v_impl_3550_, 0);
lean_inc(v_size_3552_);
v_size_3553_ = lean_ctor_get(v_l_3059_, 0);
v_k_3554_ = lean_ctor_get(v_l_3059_, 1);
v_v_3555_ = lean_ctor_get(v_l_3059_, 2);
v_l_3556_ = lean_ctor_get(v_l_3059_, 3);
v_r_3557_ = lean_ctor_get(v_l_3059_, 4);
lean_inc(v_r_3557_);
v___x_3558_ = lean_unsigned_to_nat(3u);
v___x_3559_ = lean_nat_mul(v___x_3558_, v_size_3552_);
v___x_3560_ = lean_nat_dec_lt(v___x_3559_, v_size_3553_);
lean_dec(v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_dec(v_r_3557_);
v___x_3561_ = lean_nat_add(v___x_3551_, v_size_3553_);
v___x_3562_ = lean_nat_add(v___x_3561_, v_size_3552_);
lean_dec(v_size_3552_);
lean_dec(v___x_3561_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_impl_3550_);
lean_ctor_set(v___x_3062_, 0, v___x_3562_);
v___x_3564_ = v___x_3062_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_impl_3550_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
else
{
lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3631_; 
lean_inc(v_l_3556_);
lean_inc(v_v_3555_);
lean_inc(v_k_3554_);
lean_inc(v_size_3553_);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; lean_object* v_unused_3633_; lean_object* v_unused_3634_; lean_object* v_unused_3635_; lean_object* v_unused_3636_; 
v_unused_3632_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3633_);
v_unused_3634_ = lean_ctor_get(v_l_3059_, 2);
lean_dec(v_unused_3634_);
v_unused_3635_ = lean_ctor_get(v_l_3059_, 1);
lean_dec(v_unused_3635_);
v_unused_3636_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3636_);
v___x_3567_ = v_l_3059_;
v_isShared_3568_ = v_isSharedCheck_3631_;
goto v_resetjp_3566_;
}
else
{
lean_dec(v_l_3059_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3631_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v_size_3569_; lean_object* v_size_3570_; lean_object* v_k_3571_; lean_object* v_v_3572_; lean_object* v_l_3573_; lean_object* v_r_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_size_3569_ = lean_ctor_get(v_l_3556_, 0);
v_size_3570_ = lean_ctor_get(v_r_3557_, 0);
v_k_3571_ = lean_ctor_get(v_r_3557_, 1);
v_v_3572_ = lean_ctor_get(v_r_3557_, 2);
v_l_3573_ = lean_ctor_get(v_r_3557_, 3);
v_r_3574_ = lean_ctor_get(v_r_3557_, 4);
v___x_3575_ = lean_unsigned_to_nat(2u);
v___x_3576_ = lean_nat_mul(v___x_3575_, v_size_3569_);
v___x_3577_ = lean_nat_dec_lt(v_size_3570_, v___x_3576_);
lean_dec(v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3606_; 
lean_inc(v_r_3574_);
lean_inc(v_l_3573_);
lean_inc(v_v_3572_);
lean_inc(v_k_3571_);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_r_3557_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; lean_object* v_unused_3608_; lean_object* v_unused_3609_; lean_object* v_unused_3610_; lean_object* v_unused_3611_; 
v_unused_3607_ = lean_ctor_get(v_r_3557_, 4);
lean_dec(v_unused_3607_);
v_unused_3608_ = lean_ctor_get(v_r_3557_, 3);
lean_dec(v_unused_3608_);
v_unused_3609_ = lean_ctor_get(v_r_3557_, 2);
lean_dec(v_unused_3609_);
v_unused_3610_ = lean_ctor_get(v_r_3557_, 1);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_r_3557_, 0);
lean_dec(v_unused_3611_);
v___x_3579_ = v_r_3557_;
v_isShared_3580_ = v_isSharedCheck_3606_;
goto v_resetjp_3578_;
}
else
{
lean_dec(v_r_3557_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3606_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___x_3594_; lean_object* v___y_3596_; 
v___x_3581_ = lean_nat_add(v___x_3551_, v_size_3553_);
lean_dec(v_size_3553_);
v___x_3582_ = lean_nat_add(v___x_3581_, v_size_3552_);
lean_dec(v___x_3581_);
v___x_3594_ = lean_nat_add(v___x_3551_, v_size_3569_);
if (lean_obj_tag(v_l_3573_) == 0)
{
lean_object* v_size_3604_; 
v_size_3604_ = lean_ctor_get(v_l_3573_, 0);
lean_inc(v_size_3604_);
v___y_3596_ = v_size_3604_;
goto v___jp_3595_;
}
else
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_unsigned_to_nat(0u);
v___y_3596_ = v___x_3605_;
goto v___jp_3595_;
}
v___jp_3583_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = lean_nat_add(v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec(v___y_3585_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 4, v_impl_3550_);
lean_ctor_set(v___x_3579_, 3, v_r_3574_);
lean_ctor_set(v___x_3579_, 2, v_v_3058_);
lean_ctor_set(v___x_3579_, 1, v_k_3057_);
lean_ctor_set(v___x_3579_, 0, v___x_3587_);
v___x_3589_ = v___x_3579_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3593_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3593_, 3, v_r_3574_);
lean_ctor_set(v_reuseFailAlloc_3593_, 4, v_impl_3550_);
v___x_3589_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3591_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 4, v___x_3589_);
lean_ctor_set(v___x_3567_, 3, v___y_3584_);
lean_ctor_set(v___x_3567_, 2, v_v_3572_);
lean_ctor_set(v___x_3567_, 1, v_k_3571_);
lean_ctor_set(v___x_3567_, 0, v___x_3582_);
v___x_3591_ = v___x_3567_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3571_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3572_);
lean_ctor_set(v_reuseFailAlloc_3592_, 3, v___y_3584_);
lean_ctor_set(v_reuseFailAlloc_3592_, 4, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
v___jp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3597_ = lean_nat_add(v___x_3594_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec(v___x_3594_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_l_3573_);
lean_ctor_set(v___x_3062_, 3, v_l_3556_);
lean_ctor_set(v___x_3062_, 2, v_v_3555_);
lean_ctor_set(v___x_3062_, 1, v_k_3554_);
lean_ctor_set(v___x_3062_, 0, v___x_3597_);
v___x_3599_ = v___x_3062_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_k_3554_);
lean_ctor_set(v_reuseFailAlloc_3603_, 2, v_v_3555_);
lean_ctor_set(v_reuseFailAlloc_3603_, 3, v_l_3556_);
lean_ctor_set(v_reuseFailAlloc_3603_, 4, v_l_3573_);
v___x_3599_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_nat_add(v___x_3551_, v_size_3552_);
lean_dec(v_size_3552_);
if (lean_obj_tag(v_r_3574_) == 0)
{
lean_object* v_size_3601_; 
v_size_3601_ = lean_ctor_get(v_r_3574_, 0);
lean_inc(v_size_3601_);
v___y_3584_ = v___x_3599_;
v___y_3585_ = v___x_3600_;
v___y_3586_ = v_size_3601_;
goto v___jp_3583_;
}
else
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_unsigned_to_nat(0u);
v___y_3584_ = v___x_3599_;
v___y_3585_ = v___x_3600_;
v___y_3586_ = v___x_3602_;
goto v___jp_3583_;
}
}
}
}
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_del_object(v___x_3062_);
v___x_3612_ = lean_nat_add(v___x_3551_, v_size_3553_);
lean_dec(v_size_3553_);
v___x_3613_ = lean_nat_add(v___x_3612_, v_size_3552_);
lean_dec(v___x_3612_);
v___x_3614_ = lean_nat_add(v___x_3551_, v_size_3552_);
lean_dec(v_size_3552_);
v___x_3615_ = lean_nat_add(v___x_3614_, v_size_3570_);
lean_dec(v___x_3614_);
lean_inc_ref(v_impl_3550_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 4, v_impl_3550_);
lean_ctor_set(v___x_3567_, 3, v_r_3557_);
lean_ctor_set(v___x_3567_, 2, v_v_3058_);
lean_ctor_set(v___x_3567_, 1, v_k_3057_);
lean_ctor_set(v___x_3567_, 0, v___x_3615_);
v___x_3617_ = v___x_3567_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_r_3557_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_impl_3550_);
v___x_3617_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_isSharedCheck_3624_ = !lean_is_exclusive(v_impl_3550_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; 
v_unused_3625_ = lean_ctor_get(v_impl_3550_, 4);
lean_dec(v_unused_3625_);
v_unused_3626_ = lean_ctor_get(v_impl_3550_, 3);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_impl_3550_, 2);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_impl_3550_, 1);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_impl_3550_, 0);
lean_dec(v_unused_3629_);
v___x_3619_ = v_impl_3550_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_dec(v_impl_3550_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 4, v___x_3617_);
lean_ctor_set(v___x_3619_, 3, v_l_3556_);
lean_ctor_set(v___x_3619_, 2, v_v_3555_);
lean_ctor_set(v___x_3619_, 1, v_k_3554_);
lean_ctor_set(v___x_3619_, 0, v___x_3613_);
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_k_3554_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_v_3555_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_l_3556_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v___x_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
v_size_3637_ = lean_ctor_get(v_impl_3550_, 0);
lean_inc(v_size_3637_);
v___x_3638_ = lean_nat_add(v___x_3551_, v_size_3637_);
lean_dec(v_size_3637_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_impl_3550_);
lean_ctor_set(v___x_3062_, 0, v___x_3638_);
v___x_3640_ = v___x_3062_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_impl_3550_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
else
{
if (lean_obj_tag(v_l_3059_) == 0)
{
lean_object* v_l_3642_; 
v_l_3642_ = lean_ctor_get(v_l_3059_, 3);
if (lean_obj_tag(v_l_3642_) == 0)
{
lean_object* v_r_3643_; 
lean_inc_ref(v_l_3642_);
v_r_3643_ = lean_ctor_get(v_l_3059_, 4);
lean_inc(v_r_3643_);
if (lean_obj_tag(v_r_3643_) == 0)
{
lean_object* v_size_3644_; lean_object* v_k_3645_; lean_object* v_v_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3659_; 
v_size_3644_ = lean_ctor_get(v_l_3059_, 0);
v_k_3645_ = lean_ctor_get(v_l_3059_, 1);
v_v_3646_ = lean_ctor_get(v_l_3059_, 2);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; lean_object* v_unused_3661_; 
v_unused_3660_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3661_);
v___x_3648_ = v_l_3059_;
v_isShared_3649_ = v_isSharedCheck_3659_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_v_3646_);
lean_inc(v_k_3645_);
lean_inc(v_size_3644_);
lean_dec(v_l_3059_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3659_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_size_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v_size_3650_ = lean_ctor_get(v_r_3643_, 0);
v___x_3651_ = lean_nat_add(v___x_3551_, v_size_3644_);
lean_dec(v_size_3644_);
v___x_3652_ = lean_nat_add(v___x_3551_, v_size_3650_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_impl_3550_);
lean_ctor_set(v___x_3648_, 3, v_r_3643_);
lean_ctor_set(v___x_3648_, 2, v_v_3058_);
lean_ctor_set(v___x_3648_, 1, v_k_3057_);
lean_ctor_set(v___x_3648_, 0, v___x_3652_);
v___x_3654_ = v___x_3648_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3658_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3658_, 3, v_r_3643_);
lean_ctor_set(v_reuseFailAlloc_3658_, 4, v_impl_3550_);
v___x_3654_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3654_);
lean_ctor_set(v___x_3062_, 3, v_l_3642_);
lean_ctor_set(v___x_3062_, 2, v_v_3646_);
lean_ctor_set(v___x_3062_, 1, v_k_3645_);
lean_ctor_set(v___x_3062_, 0, v___x_3651_);
v___x_3656_ = v___x_3062_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_k_3645_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_v_3646_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_l_3642_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
else
{
lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3674_; 
v_k_3662_ = lean_ctor_get(v_l_3059_, 1);
v_v_3663_ = lean_ctor_get(v_l_3059_, 2);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; lean_object* v_unused_3676_; lean_object* v_unused_3677_; 
v_unused_3675_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3676_);
v_unused_3677_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3677_);
v___x_3665_ = v_l_3059_;
v_isShared_3666_ = v_isSharedCheck_3674_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_v_3663_);
lean_inc(v_k_3662_);
lean_dec(v_l_3059_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3674_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3667_ = lean_unsigned_to_nat(3u);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 3, v_r_3643_);
lean_ctor_set(v___x_3665_, 2, v_v_3058_);
lean_ctor_set(v___x_3665_, 1, v_k_3057_);
lean_ctor_set(v___x_3665_, 0, v___x_3551_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3673_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3673_, 3, v_r_3643_);
lean_ctor_set(v_reuseFailAlloc_3673_, 4, v_r_3643_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3669_);
lean_ctor_set(v___x_3062_, 3, v_l_3642_);
lean_ctor_set(v___x_3062_, 2, v_v_3663_);
lean_ctor_set(v___x_3062_, 1, v_k_3662_);
lean_ctor_set(v___x_3062_, 0, v___x_3667_);
v___x_3671_ = v___x_3062_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3662_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3663_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_l_3642_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
else
{
lean_object* v_r_3678_; 
v_r_3678_ = lean_ctor_get(v_l_3059_, 4);
lean_inc(v_r_3678_);
if (lean_obj_tag(v_r_3678_) == 0)
{
lean_object* v_k_3679_; lean_object* v_v_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3703_; 
lean_inc(v_l_3642_);
v_k_3679_ = lean_ctor_get(v_l_3059_, 1);
v_v_3680_ = lean_ctor_get(v_l_3059_, 2);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_l_3059_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; lean_object* v_unused_3705_; lean_object* v_unused_3706_; 
v_unused_3704_ = lean_ctor_get(v_l_3059_, 4);
lean_dec(v_unused_3704_);
v_unused_3705_ = lean_ctor_get(v_l_3059_, 3);
lean_dec(v_unused_3705_);
v_unused_3706_ = lean_ctor_get(v_l_3059_, 0);
lean_dec(v_unused_3706_);
v___x_3682_ = v_l_3059_;
v_isShared_3683_ = v_isSharedCheck_3703_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_v_3680_);
lean_inc(v_k_3679_);
lean_dec(v_l_3059_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3703_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v_k_3684_; lean_object* v_v_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3699_; 
v_k_3684_ = lean_ctor_get(v_r_3678_, 1);
v_v_3685_ = lean_ctor_get(v_r_3678_, 2);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_r_3678_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; lean_object* v_unused_3701_; lean_object* v_unused_3702_; 
v_unused_3700_ = lean_ctor_get(v_r_3678_, 4);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_r_3678_, 3);
lean_dec(v_unused_3701_);
v_unused_3702_ = lean_ctor_get(v_r_3678_, 0);
lean_dec(v_unused_3702_);
v___x_3687_ = v_r_3678_;
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_v_3685_);
lean_inc(v_k_3684_);
lean_dec(v_r_3678_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3699_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_unsigned_to_nat(3u);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 4, v_l_3642_);
lean_ctor_set(v___x_3687_, 3, v_l_3642_);
lean_ctor_set(v___x_3687_, 2, v_v_3680_);
lean_ctor_set(v___x_3687_, 1, v_k_3679_);
lean_ctor_set(v___x_3687_, 0, v___x_3551_);
v___x_3691_ = v___x_3687_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v_l_3642_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v_l_3642_);
v___x_3691_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 4, v_l_3642_);
lean_ctor_set(v___x_3682_, 2, v_v_3058_);
lean_ctor_set(v___x_3682_, 1, v_k_3057_);
lean_ctor_set(v___x_3682_, 0, v___x_3551_);
v___x_3693_ = v___x_3682_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_l_3642_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_l_3642_);
v___x_3693_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3695_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v___x_3693_);
lean_ctor_set(v___x_3062_, 3, v___x_3691_);
lean_ctor_set(v___x_3062_, 2, v_v_3685_);
lean_ctor_set(v___x_3062_, 1, v_k_3684_);
lean_ctor_set(v___x_3062_, 0, v___x_3689_);
v___x_3695_ = v___x_3062_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_k_3684_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_v_3685_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3696_, 4, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = lean_unsigned_to_nat(2u);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_r_3678_);
lean_ctor_set(v___x_3062_, 0, v___x_3707_);
v___x_3709_ = v___x_3062_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_r_3678_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v___x_3712_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 4, v_l_3059_);
lean_ctor_set(v___x_3062_, 0, v___x_3551_);
v___x_3712_ = v___x_3062_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3057_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3058_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_l_3059_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_l_3059_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
}
}
else
{
return v_t_3056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3716_, lean_object* v_t_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3716_, v_t_3717_);
lean_dec(v_k_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3719_, lean_object* v_x_3720_){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3719_, v_x_3720_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3722_, lean_object* v_x_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3722_, v_x_3723_);
lean_dec(v_declName_3722_);
return v_res_3724_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3727_ = l_Lean_stringToMessageData(v___x_3726_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; lean_object* v_env_3737_; lean_object* v___f_3738_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___x_3783_; 
v___x_3736_ = lean_st_ref_get(v___y_3734_);
v_env_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc_ref(v_env_3737_);
lean_dec(v___x_3736_);
lean_inc(v_declName_3728_);
v___f_3738_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3738_, 0, v_declName_3728_);
v___x_3783_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3737_, v_declName_3728_);
lean_dec_ref(v_env_3737_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_dec(v_declName_3728_);
v___y_3740_ = v___y_3732_;
v___y_3741_ = v___y_3734_;
goto v___jp_3739_;
}
else
{
uint8_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec_ref(v___x_3783_);
lean_dec_ref(v___f_3738_);
v___x_3784_ = 0;
v___x_3785_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3786_ = l_Lean_MessageData_ofConstName(v_declName_3728_, v___x_3784_);
v___x_3787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3785_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
v___x_3788_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3787_);
lean_ctor_set(v___x_3789_, 1, v___x_3788_);
v___x_3790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3789_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3790_;
}
v___jp_3739_:
{
lean_object* v___x_3742_; lean_object* v_env_3743_; lean_object* v_nextMacroScope_3744_; lean_object* v_ngen_3745_; lean_object* v_auxDeclNGen_3746_; lean_object* v_traceState_3747_; lean_object* v_messages_3748_; lean_object* v_infoState_3749_; lean_object* v_snapshotTasks_3750_; lean_object* v_newDecls_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3781_; 
v___x_3742_ = lean_st_ref_take(v___y_3741_);
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
v_nextMacroScope_3744_ = lean_ctor_get(v___x_3742_, 1);
v_ngen_3745_ = lean_ctor_get(v___x_3742_, 2);
v_auxDeclNGen_3746_ = lean_ctor_get(v___x_3742_, 3);
v_traceState_3747_ = lean_ctor_get(v___x_3742_, 4);
v_messages_3748_ = lean_ctor_get(v___x_3742_, 6);
v_infoState_3749_ = lean_ctor_get(v___x_3742_, 7);
v_snapshotTasks_3750_ = lean_ctor_get(v___x_3742_, 8);
v_newDecls_3751_ = lean_ctor_get(v___x_3742_, 9);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; 
v_unused_3782_ = lean_ctor_get(v___x_3742_, 5);
lean_dec(v_unused_3782_);
v___x_3753_ = v___x_3742_;
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_newDecls_3751_);
lean_inc(v_snapshotTasks_3750_);
lean_inc(v_infoState_3749_);
lean_inc(v_messages_3748_);
lean_inc(v_traceState_3747_);
lean_inc(v_auxDeclNGen_3746_);
lean_inc(v_ngen_3745_);
lean_inc(v_nextMacroScope_3744_);
lean_inc(v_env_3743_);
lean_dec(v___x_3742_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3781_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
v___x_3755_ = l_Lean_docStringExt;
v___x_3756_ = lean_box(2);
v___x_3757_ = lean_box(0);
v___x_3758_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3755_, v_env_3743_, v___f_3738_, v___x_3756_, v___x_3757_);
v___x_3759_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 5, v___x_3759_);
lean_ctor_set(v___x_3753_, 0, v___x_3758_);
v___x_3761_ = v___x_3753_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_nextMacroScope_3744_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_ngen_3745_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_auxDeclNGen_3746_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_traceState_3747_);
lean_ctor_set(v_reuseFailAlloc_3780_, 5, v___x_3759_);
lean_ctor_set(v_reuseFailAlloc_3780_, 6, v_messages_3748_);
lean_ctor_set(v_reuseFailAlloc_3780_, 7, v_infoState_3749_);
lean_ctor_set(v_reuseFailAlloc_3780_, 8, v_snapshotTasks_3750_);
lean_ctor_set(v_reuseFailAlloc_3780_, 9, v_newDecls_3751_);
v___x_3761_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v_mctx_3764_; lean_object* v_zetaDeltaFVarIds_3765_; lean_object* v_postponed_3766_; lean_object* v_diag_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3778_; 
v___x_3762_ = lean_st_ref_set(v___y_3741_, v___x_3761_);
v___x_3763_ = lean_st_ref_take(v___y_3740_);
v_mctx_3764_ = lean_ctor_get(v___x_3763_, 0);
v_zetaDeltaFVarIds_3765_ = lean_ctor_get(v___x_3763_, 2);
v_postponed_3766_ = lean_ctor_get(v___x_3763_, 3);
v_diag_3767_ = lean_ctor_get(v___x_3763_, 4);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; 
v_unused_3779_ = lean_ctor_get(v___x_3763_, 1);
lean_dec(v_unused_3779_);
v___x_3769_ = v___x_3763_;
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_diag_3767_);
lean_inc(v_postponed_3766_);
lean_inc(v_zetaDeltaFVarIds_3765_);
lean_inc(v_mctx_3764_);
lean_dec(v___x_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3778_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3771_; lean_object* v___x_3773_; 
v___x_3771_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v___x_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_mctx_3764_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_zetaDeltaFVarIds_3765_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_postponed_3766_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v_diag_3767_);
v___x_3773_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = lean_st_ref_set(v___y_3740_, v___x_3773_);
v___x_3775_ = lean_box(0);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
return v_res_3799_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3802_ = l_Lean_stringToMessageData(v___x_3801_);
return v___x_3802_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3805_ = l_Lean_stringToMessageData(v___x_3804_);
return v___x_3805_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3808_ = l_Lean_stringToMessageData(v___x_3807_);
return v___x_3808_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3811_ = l_Lean_stringToMessageData(v___x_3810_);
return v___x_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v___x_3820_; lean_object* v_env_3821_; uint8_t v___x_3822_; lean_object* v___x_3823_; 
v___x_3820_ = lean_st_ref_get(v_a_3818_);
v_env_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc_ref(v_env_3821_);
lean_dec(v___x_3820_);
v___x_3822_ = 1;
lean_inc(v_declName_3812_);
v___x_3823_ = l_Lean_findInternalDocString_x3f(v_env_3821_, v_declName_3812_, v___x_3822_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref(v___x_3823_);
if (lean_obj_tag(v_a_3824_) == 1)
{
lean_object* v_val_3825_; 
v_val_3825_ = lean_ctor_get(v_a_3824_, 0);
lean_inc(v_val_3825_);
lean_dec_ref(v_a_3824_);
if (lean_obj_tag(v_val_3825_) == 0)
{
lean_object* v_val_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3848_; 
v_val_3826_ = lean_ctor_get(v_val_3825_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_val_3825_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3828_ = v_val_3825_;
v_isShared_3829_ = v_isSharedCheck_3848_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_val_3826_);
lean_dec(v_val_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3848_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Lean_removeBuiltinDocString(v_declName_3812_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v___x_3831_; 
lean_dec_ref(v___x_3830_);
lean_del_object(v___x_3828_);
lean_inc(v_declName_3812_);
v___x_3831_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; 
lean_dec_ref(v___x_3831_);
v___x_3832_ = l_Lean_addVersoDocStringFromString(v_declName_3812_, v_val_3826_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
return v___x_3832_;
}
else
{
lean_dec(v_val_3826_);
lean_dec(v_declName_3812_);
return v___x_3831_;
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3847_; 
lean_dec(v_val_3826_);
lean_dec(v_declName_3812_);
v_a_3833_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3835_ = v___x_3830_;
v_isShared_3836_ = v_isSharedCheck_3847_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3830_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3847_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v_ref_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v_ref_3837_ = lean_ctor_get(v_a_3817_, 5);
v___x_3838_ = lean_io_error_to_string(v_a_3833_);
if (v_isShared_3829_ == 0)
{
lean_ctor_set_tag(v___x_3828_, 3);
lean_ctor_set(v___x_3828_, 0, v___x_3838_);
v___x_3840_ = v___x_3828_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3841_ = l_Lean_MessageData_ofFormat(v___x_3840_);
lean_inc(v_ref_3837_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_ref_3837_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3842_);
v___x_3844_ = v___x_3835_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
}
}
else
{
lean_object* v___x_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_val_3825_);
v___x_3849_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3850_ = 0;
v___x_3851_ = l_Lean_MessageData_ofConstName(v_declName_3812_, v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3854_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
return v___x_3855_;
}
}
else
{
lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec(v_a_3824_);
v___x_3856_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3857_ = 0;
v___x_3858_ = l_Lean_MessageData_ofConstName(v_declName_3812_, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3856_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3859_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3861_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
return v___x_3862_;
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v_declName_3812_);
v_a_3863_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3865_ = v___x_3823_;
v_isShared_3866_ = v_isSharedCheck_3875_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3823_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3875_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v_ref_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
v_ref_3867_ = lean_ctor_get(v_a_3817_, 5);
v___x_3868_ = lean_io_error_to_string(v_a_3863_);
v___x_3869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
v___x_3870_ = l_Lean_MessageData_ofFormat(v___x_3869_);
lean_inc(v_ref_3867_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v_ref_3867_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 0, v___x_3871_);
v___x_3873_ = v___x_3865_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_makeDocStringVerso(v_declName_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3885_, lean_object* v_k_3886_, lean_object* v_t_3887_, lean_object* v_h_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3886_, v_t_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3890_, lean_object* v_k_3891_, lean_object* v_t_3892_, lean_object* v_h_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3890_, v_k_3891_, v_t_3892_, v_h_3893_);
lean_dec(v_k_3891_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3895_, lean_object* v_binders_3896_, lean_object* v_docComment_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_options_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; 
v_options_3905_ = lean_ctor_get(v_a_3902_, 2);
v___x_3906_ = l_Lean_doc_verso;
v___x_3907_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_3905_, v___x_3906_);
v___x_3908_ = l_Lean_addDocStringOf(v___x_3907_, v_declName_3895_, v_binders_3896_, v_docComment_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3909_, lean_object* v_binders_3910_, lean_object* v_docComment_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_addDocString(v_declName_3909_, v_binders_3910_, v_docComment_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
lean_dec(v_a_3917_);
lean_dec_ref(v_a_3916_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3920_, lean_object* v_binders_3921_, lean_object* v_docString_x3f_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3922_) == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_dec(v_binders_3921_);
lean_dec(v_declName_3920_);
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
else
{
lean_object* v_val_3932_; lean_object* v___x_3933_; 
v_val_3932_ = lean_ctor_get(v_docString_x3f_3922_, 0);
lean_inc(v_val_3932_);
lean_dec_ref(v_docString_x3f_3922_);
v___x_3933_ = l_Lean_addDocString(v_declName_3920_, v_binders_3921_, v_val_3932_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
return v___x_3933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3934_, lean_object* v_binders_3935_, lean_object* v_docString_x3f_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
lean_object* v_res_3944_; 
v_res_3944_ = l_Lean_addDocString_x27(v_declName_3934_, v_binders_3935_, v_docString_x3f_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v_nextMacroScope_3950_; lean_object* v_ngen_3951_; lean_object* v_auxDeclNGen_3952_; lean_object* v_traceState_3953_; lean_object* v_messages_3954_; lean_object* v_infoState_3955_; lean_object* v_snapshotTasks_3956_; lean_object* v_newDecls_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3983_; 
v___x_3949_ = lean_st_ref_take(v___y_3947_);
v_nextMacroScope_3950_ = lean_ctor_get(v___x_3949_, 1);
v_ngen_3951_ = lean_ctor_get(v___x_3949_, 2);
v_auxDeclNGen_3952_ = lean_ctor_get(v___x_3949_, 3);
v_traceState_3953_ = lean_ctor_get(v___x_3949_, 4);
v_messages_3954_ = lean_ctor_get(v___x_3949_, 6);
v_infoState_3955_ = lean_ctor_get(v___x_3949_, 7);
v_snapshotTasks_3956_ = lean_ctor_get(v___x_3949_, 8);
v_newDecls_3957_ = lean_ctor_get(v___x_3949_, 9);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; lean_object* v_unused_3985_; 
v_unused_3984_ = lean_ctor_get(v___x_3949_, 5);
lean_dec(v_unused_3984_);
v_unused_3985_ = lean_ctor_get(v___x_3949_, 0);
lean_dec(v_unused_3985_);
v___x_3959_ = v___x_3949_;
v_isShared_3960_ = v_isSharedCheck_3983_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_newDecls_3957_);
lean_inc(v_snapshotTasks_3956_);
lean_inc(v_infoState_3955_);
lean_inc(v_messages_3954_);
lean_inc(v_traceState_3953_);
lean_inc(v_auxDeclNGen_3952_);
lean_inc(v_ngen_3951_);
lean_inc(v_nextMacroScope_3950_);
lean_dec(v___x_3949_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3983_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3961_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 5, v___x_3961_);
lean_ctor_set(v___x_3959_, 0, v_env_3945_);
v___x_3963_ = v___x_3959_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_env_3945_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_nextMacroScope_3950_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_ngen_3951_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_auxDeclNGen_3952_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_traceState_3953_);
lean_ctor_set(v_reuseFailAlloc_3982_, 5, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3982_, 6, v_messages_3954_);
lean_ctor_set(v_reuseFailAlloc_3982_, 7, v_infoState_3955_);
lean_ctor_set(v_reuseFailAlloc_3982_, 8, v_snapshotTasks_3956_);
lean_ctor_set(v_reuseFailAlloc_3982_, 9, v_newDecls_3957_);
v___x_3963_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v_mctx_3966_; lean_object* v_zetaDeltaFVarIds_3967_; lean_object* v_postponed_3968_; lean_object* v_diag_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3980_; 
v___x_3964_ = lean_st_ref_set(v___y_3947_, v___x_3963_);
v___x_3965_ = lean_st_ref_take(v___y_3946_);
v_mctx_3966_ = lean_ctor_get(v___x_3965_, 0);
v_zetaDeltaFVarIds_3967_ = lean_ctor_get(v___x_3965_, 2);
v_postponed_3968_ = lean_ctor_get(v___x_3965_, 3);
v_diag_3969_ = lean_ctor_get(v___x_3965_, 4);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; 
v_unused_3981_ = lean_ctor_get(v___x_3965_, 1);
lean_dec(v_unused_3981_);
v___x_3971_ = v___x_3965_;
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_diag_3969_);
lean_inc(v_postponed_3968_);
lean_inc(v_zetaDeltaFVarIds_3967_);
lean_inc(v_mctx_3966_);
lean_dec(v___x_3965_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 1, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_mctx_3966_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_zetaDeltaFVarIds_3967_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_postponed_3968_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_diag_3969_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = lean_st_ref_set(v___y_3946_, v___x_3975_);
v___x_3977_ = lean_box(0);
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3977_);
return v___x_3978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec(v___y_3987_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v___x_3999_; lean_object* v_env_4000_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_3999_ = lean_st_ref_get(v___y_3997_);
v_env_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_ref(v_env_4000_);
lean_dec(v___x_3999_);
v___x_4001_ = l_Lean_getMainModuleDoc(v_env_4000_);
v___x_4002_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4001_);
lean_dec_ref(v___x_4001_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec_ref(v_docs_3991_);
v___x_4003_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4004_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4003_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
return v___x_4004_;
}
else
{
lean_object* v___x_4005_; lean_object* v_env_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_st_ref_get(v___y_3997_);
v_env_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_ref(v_env_4006_);
lean_dec(v___x_4005_);
v___x_4007_ = l_Lean_addVersoModuleDocSnippet(v_env_4006_, v_docs_3991_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
v___x_4009_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_4010_ = l_Lean_stringToMessageData(v_a_4008_);
v___x_4011_ = l_Lean_indentD(v___x_4010_);
v___x_4012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4009_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v___x_4013_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4012_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
return v___x_4013_;
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4015_; 
v_a_4014_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4007_);
v___x_4015_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4014_, v___y_3995_, v___y_3997_);
return v___x_4015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4025_, lean_object* v_docComment_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Lean_versoModDocString(v_range_4025_, v_docComment_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref(v___x_4034_);
v___x_4036_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_a_4035_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
return v___x_4036_;
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4034_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4034_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4045_, lean_object* v_docComment_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l_Lean_addVersoModDocString(v_range_4045_, v_docComment_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
lean_dec_ref(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_docComment_4046_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4055_, v___y_4059_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4072_;
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
