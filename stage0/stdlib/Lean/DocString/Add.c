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
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_versoDocString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_versoDocString___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object* v___x_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4___boxed(lean_object* v___x_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_validateDocComment___redArg___lam__4(v___x_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_docstring_96_){
_start:
{
lean_object* v_toApplicative_97_; lean_object* v_toBind_98_; lean_object* v_toPure_99_; lean_object* v_str_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___f_104_; lean_object* v___y_106_; 
v_toApplicative_97_ = lean_ctor_get(v_inst_91_, 0);
v_toBind_98_ = lean_ctor_get(v_inst_91_, 1);
lean_inc(v_toBind_98_);
v_toPure_99_ = lean_ctor_get(v_toApplicative_97_, 1);
lean_inc(v_toPure_99_);
v_str_100_ = l_Lean_TSyntax_getDocString(v_docstring_96_);
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = l_Lean_Syntax_getArg(v_docstring_96_, v___x_101_);
v___x_103_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_102_);
lean_dec(v___x_102_);
lean_inc(v_toPure_99_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__0), 2, 1);
lean_closure_set(v___f_104_, 0, v_toPure_99_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
v___y_106_ = v___x_112_;
goto v___jp_105_;
}
else
{
lean_object* v_val_113_; uint8_t v___x_114_; lean_object* v___x_115_; 
v_val_113_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_val_113_);
lean_dec_ref(v___x_103_);
v___x_114_ = 0;
v___x_115_ = l_Lean_SourceInfo_getPos_x3f(v_val_113_, v___x_114_);
lean_dec(v_val_113_);
v___y_106_ = v___x_115_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
lean_inc(v_toBind_98_);
lean_inc_ref(v_str_100_);
v___f_107_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__2), 10, 9);
lean_closure_set(v___f_107_, 0, v_toPure_99_);
lean_closure_set(v___f_107_, 1, v___y_106_);
lean_closure_set(v___f_107_, 2, v_str_100_);
lean_closure_set(v___f_107_, 3, v_inst_91_);
lean_closure_set(v___f_107_, 4, v_inst_93_);
lean_closure_set(v___f_107_, 5, v_inst_94_);
lean_closure_set(v___f_107_, 6, v_inst_95_);
lean_closure_set(v___f_107_, 7, v_toBind_98_);
lean_closure_set(v___f_107_, 8, v___f_104_);
v___x_108_ = l_Lean_rewriteManualLinksCore(v_str_100_);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__4___boxed), 2, 1);
lean_closure_set(v___f_109_, 0, v___x_108_);
v___x_110_ = lean_apply_2(v_inst_92_, lean_box(0), v___f_109_);
v___x_111_ = lean_apply_4(v_toBind_98_, lean_box(0), lean_box(0), v___x_110_, v___f_107_);
return v___x_111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_docstring_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_validateDocComment___redArg(v_inst_116_, v_inst_117_, v_inst_118_, v_inst_119_, v_inst_120_, v_docstring_121_);
lean_dec(v_docstring_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* v_m_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_docstring_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_validateDocComment___redArg(v_inst_124_, v_inst_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_docstring_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* v_m_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_docstring_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_validateDocComment(v_m_131_, v_inst_132_, v_inst_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_docstring_137_);
lean_dec(v_docstring_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* v_toApplicative_139_, lean_object* v_____s_140_){
_start:
{
lean_object* v_toPure_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_toPure_141_ = lean_ctor_get(v_toApplicative_139_, 1);
lean_inc(v_toPure_141_);
lean_dec_ref(v_toApplicative_139_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_2(v_toPure_141_, lean_box(0), v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* v_toApplicative_144_, lean_object* v_____r_145_){
_start:
{
lean_object* v_toPure_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_toPure_146_ = lean_ctor_get(v_toApplicative_144_, 1);
lean_inc(v_toPure_146_);
lean_dec_ref(v_toApplicative_144_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_2(v_toPure_146_, lean_box(0), v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v_toApplicative_149_, lean_object* v___x_150_, lean_object* v_____r_151_){
_start:
{
lean_object* v_toPure_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_toPure_152_ = lean_ctor_get(v_toApplicative_149_, 1);
lean_inc(v_toPure_152_);
lean_dec_ref(v_toApplicative_149_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_150_);
v___x_154_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_text_156_, lean_object* v_fst_157_, lean_object* v_snd_158_, uint8_t v___x_159_, lean_object* v_logMessage_160_, lean_object* v_toBind_161_, lean_object* v___f_162_, lean_object* v_____do__lift_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_164_ = l_Lean_FileMap_toPosition(v_text_156_, v_fst_157_);
v___x_165_ = lean_box(0);
v___x_166_ = 2;
v___x_167_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_168_ = l_Lean_Parser_Error_toString(v_snd_158_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = l_Lean_MessageData_ofFormat(v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_171_, 0, v_____do__lift_163_);
lean_ctor_set(v___x_171_, 1, v___x_164_);
lean_ctor_set(v___x_171_, 2, v___x_165_);
lean_ctor_set(v___x_171_, 3, v___x_167_);
lean_ctor_set(v___x_171_, 4, v___x_170_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*5, v___x_159_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*5 + 1, v___x_166_);
lean_ctor_set_uint8(v___x_171_, sizeof(void*)*5 + 2, v___x_159_);
v___x_172_ = lean_apply_1(v_logMessage_160_, v___x_171_);
v___x_173_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_172_, v___f_162_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object* v_text_174_, lean_object* v_fst_175_, lean_object* v_snd_176_, lean_object* v___x_177_, lean_object* v_logMessage_178_, lean_object* v_toBind_179_, lean_object* v___f_180_, lean_object* v_____do__lift_181_){
_start:
{
uint8_t v___x_1930__boxed_182_; lean_object* v_res_183_; 
v___x_1930__boxed_182_ = lean_unbox(v___x_177_);
v_res_183_ = l_Lean_parseVersoDocString___redArg___lam__3(v_text_174_, v_fst_175_, v_snd_176_, v___x_1930__boxed_182_, v_logMessage_178_, v_toBind_179_, v___f_180_, v_____do__lift_181_);
lean_dec(v_fst_175_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_184_, uint8_t v___x_185_, lean_object* v_logMessage_186_, lean_object* v_toBind_187_, lean_object* v___f_188_, lean_object* v_getFileName_189_, lean_object* v_a_190_, lean_object* v_x_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_snd_193_; lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_snd_193_ = lean_ctor_get(v_a_190_, 1);
lean_inc(v_snd_193_);
v_fst_194_ = lean_ctor_get(v_a_190_, 0);
lean_inc(v_fst_194_);
lean_dec_ref(v_a_190_);
v_snd_195_ = lean_ctor_get(v_snd_193_, 1);
lean_inc(v_snd_195_);
lean_dec(v_snd_193_);
v___x_196_ = lean_box(v___x_185_);
lean_inc(v_toBind_187_);
v___f_197_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_197_, 0, v_text_184_);
lean_closure_set(v___f_197_, 1, v_fst_194_);
lean_closure_set(v___f_197_, 2, v_snd_195_);
lean_closure_set(v___f_197_, 3, v___x_196_);
lean_closure_set(v___f_197_, 4, v_logMessage_186_);
lean_closure_set(v___f_197_, 5, v_toBind_187_);
lean_closure_set(v___f_197_, 6, v___f_188_);
v___x_198_ = lean_apply_4(v_toBind_187_, lean_box(0), lean_box(0), v_getFileName_189_, v___f_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_199_, lean_object* v___x_200_, lean_object* v_logMessage_201_, lean_object* v_toBind_202_, lean_object* v___f_203_, lean_object* v_getFileName_204_, lean_object* v_a_205_, lean_object* v_x_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_1964__boxed_208_; lean_object* v_res_209_; 
v___x_1964__boxed_208_ = lean_unbox(v___x_200_);
v_res_209_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_199_, v___x_1964__boxed_208_, v_logMessage_201_, v_toBind_202_, v___f_203_, v_getFileName_204_, v_a_205_, v_x_206_, v___y_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_text_212_, lean_object* v_pos_213_, lean_object* v_source_214_, uint8_t v___x_215_, lean_object* v_logMessage_216_, lean_object* v_toBind_217_, lean_object* v___f_218_, lean_object* v_____do__lift_219_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint32_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_220_ = l_Lean_FileMap_toPosition(v_text_212_, v_pos_213_);
v___x_221_ = lean_box(0);
v___x_222_ = 2;
v___x_223_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_224_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_225_ = lean_string_utf8_get(v_source_214_, v_pos_213_);
v___x_226_ = lean_string_push(v___x_223_, v___x_225_);
v___x_227_ = lean_string_append(v___x_224_, v___x_226_);
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_229_ = lean_string_append(v___x_227_, v___x_228_);
v___x_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
v___x_231_ = l_Lean_MessageData_ofFormat(v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_232_, 0, v_____do__lift_219_);
lean_ctor_set(v___x_232_, 1, v___x_220_);
lean_ctor_set(v___x_232_, 2, v___x_221_);
lean_ctor_set(v___x_232_, 3, v___x_223_);
lean_ctor_set(v___x_232_, 4, v___x_231_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*5, v___x_215_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*5 + 1, v___x_222_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*5 + 2, v___x_215_);
v___x_233_ = lean_apply_1(v_logMessage_216_, v___x_232_);
v___x_234_ = lean_apply_4(v_toBind_217_, lean_box(0), lean_box(0), v___x_233_, v___f_218_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object* v_text_235_, lean_object* v_pos_236_, lean_object* v_source_237_, lean_object* v___x_238_, lean_object* v_logMessage_239_, lean_object* v_toBind_240_, lean_object* v___f_241_, lean_object* v_____do__lift_242_){
_start:
{
uint8_t v___x_1994__boxed_243_; lean_object* v_res_244_; 
v___x_1994__boxed_243_ = lean_unbox(v___x_238_);
v_res_244_ = l_Lean_parseVersoDocString___redArg___lam__5(v_text_235_, v_pos_236_, v_source_237_, v___x_1994__boxed_243_, v_logMessage_239_, v_toBind_240_, v___f_241_, v_____do__lift_242_);
lean_dec_ref(v_source_237_);
lean_dec(v_pos_236_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_toApplicative_245_, lean_object* v_text_246_, lean_object* v_logMessage_247_, lean_object* v_toBind_248_, lean_object* v_getFileName_249_, lean_object* v_inst_250_, lean_object* v___f_251_, lean_object* v_ictx_252_, lean_object* v_source_253_, lean_object* v___f_254_, lean_object* v_env_255_, lean_object* v_____do__lift_256_, lean_object* v_____do__lift_257_, lean_object* v_val_258_, lean_object* v___y_259_, lean_object* v___x_260_, lean_object* v_____do__lift_261_){
_start:
{
lean_object* v___y_263_; lean_object* v_pmctx_286_; lean_object* v_blockCtxt_287_; lean_object* v___x_288_; lean_object* v_s_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_s_292_; uint8_t v___y_294_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
lean_inc_ref(v_env_255_);
v_pmctx_286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_286_, 0, v_env_255_);
lean_ctor_set(v_pmctx_286_, 1, v_____do__lift_256_);
lean_ctor_set(v_pmctx_286_, 2, v_____do__lift_257_);
lean_ctor_set(v_pmctx_286_, 3, v_____do__lift_261_);
lean_inc(v_val_258_);
lean_inc_ref(v_text_246_);
v_blockCtxt_287_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_246_, v_val_258_, v___y_259_);
v___x_288_ = l_Lean_Parser_mkParserState(v_source_253_);
lean_inc_ref(v___x_288_);
v_s_289_ = l_Lean_Parser_ParserState_setPos(v___x_288_, v_val_258_);
v___x_290_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_290_, 0, v_blockCtxt_287_);
v___x_291_ = l_Lean_Parser_getTokenTable(v_env_255_);
lean_inc_ref(v___x_291_);
lean_inc_ref(v_pmctx_286_);
lean_inc_ref(v_ictx_252_);
v_s_292_ = l_Lean_Parser_ParserFn_run(v___x_290_, v_ictx_252_, v_pmctx_286_, v___x_291_, v_s_289_);
lean_inc_ref(v_s_292_);
v___x_304_ = l_Lean_Parser_ParserState_allErrors(v_s_292_);
v___x_305_ = lean_array_get_size(v___x_304_);
lean_dec_ref(v___x_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
v___y_294_ = v___x_307_;
goto v___jp_293_;
}
else
{
lean_object* v_pos_308_; uint8_t v___x_309_; 
v_pos_308_ = lean_ctor_get(v_s_292_, 2);
lean_inc(v_pos_308_);
v___x_309_ = l_Lean_Parser_InputContext_atEnd(v_ictx_252_, v_pos_308_);
lean_dec(v_pos_308_);
if (v___x_309_ == 0)
{
v___y_294_ = v___x_307_;
goto v___jp_293_;
}
else
{
lean_dec_ref(v___x_291_);
lean_dec_ref(v___x_288_);
lean_dec_ref(v_pmctx_286_);
lean_dec(v___x_260_);
v___y_263_ = v_s_292_;
goto v___jp_262_;
}
}
v___jp_262_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
lean_inc_ref(v___y_263_);
v___x_264_ = l_Lean_Parser_ParserState_allErrors(v___y_263_);
v___x_265_ = lean_array_get_size(v___x_264_);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_dec_eq(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v___f_271_; size_t v_sz_272_; size_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v___y_263_);
lean_dec(v___f_254_);
lean_dec_ref(v_source_253_);
lean_dec_ref(v_ictx_252_);
v___x_268_ = lean_box(0);
v___f_269_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_269_, 0, v_toApplicative_245_);
lean_closure_set(v___f_269_, 1, v___x_268_);
v___x_270_ = lean_box(v___x_267_);
lean_inc(v_toBind_248_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_271_, 0, v_text_246_);
lean_closure_set(v___f_271_, 1, v___x_270_);
lean_closure_set(v___f_271_, 2, v_logMessage_247_);
lean_closure_set(v___f_271_, 3, v_toBind_248_);
lean_closure_set(v___f_271_, 4, v___f_269_);
lean_closure_set(v___f_271_, 5, v_getFileName_249_);
v_sz_272_ = lean_array_size(v___x_264_);
v___x_273_ = ((size_t)0ULL);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_250_, v___x_264_, v___f_271_, v_sz_272_, v___x_273_, v___x_268_);
v___x_275_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v___x_274_, v___f_251_);
return v___x_275_;
}
else
{
lean_object* v_stxStack_276_; lean_object* v_pos_277_; uint8_t v___x_278_; 
lean_dec_ref(v___x_264_);
lean_dec(v___f_251_);
lean_dec_ref(v_inst_250_);
v_stxStack_276_ = lean_ctor_get(v___y_263_, 0);
lean_inc_ref(v_stxStack_276_);
v_pos_277_ = lean_ctor_get(v___y_263_, 2);
lean_inc(v_pos_277_);
lean_dec_ref(v___y_263_);
v___x_278_ = l_Lean_Parser_InputContext_atEnd(v_ictx_252_, v_pos_277_);
lean_dec_ref(v_ictx_252_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___x_281_; 
lean_dec_ref(v_stxStack_276_);
lean_dec_ref(v_toApplicative_245_);
v___x_279_ = lean_box(v___x_278_);
lean_inc(v_toBind_248_);
v___f_280_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_280_, 0, v_text_246_);
lean_closure_set(v___f_280_, 1, v_pos_277_);
lean_closure_set(v___f_280_, 2, v_source_253_);
lean_closure_set(v___f_280_, 3, v___x_279_);
lean_closure_set(v___f_280_, 4, v_logMessage_247_);
lean_closure_set(v___f_280_, 5, v_toBind_248_);
lean_closure_set(v___f_280_, 6, v___f_254_);
v___x_281_ = lean_apply_4(v_toBind_248_, lean_box(0), lean_box(0), v_getFileName_249_, v___f_280_);
return v___x_281_;
}
else
{
lean_object* v_toPure_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v_pos_277_);
lean_dec(v___f_254_);
lean_dec_ref(v_source_253_);
lean_dec(v_getFileName_249_);
lean_dec(v_toBind_248_);
lean_dec(v_logMessage_247_);
lean_dec_ref(v_text_246_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_245_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_245_);
v___x_283_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_276_);
lean_dec_ref(v_stxStack_276_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = lean_apply_2(v_toPure_282_, lean_box(0), v___x_284_);
return v___x_285_;
}
}
}
v___jp_293_:
{
if (v___y_294_ == 0)
{
lean_dec_ref(v___x_291_);
lean_dec_ref(v___x_288_);
lean_dec_ref(v_pmctx_286_);
lean_dec(v___x_260_);
v___y_263_ = v_s_292_;
goto v___jp_262_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_pos_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_box(0);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_260_);
lean_ctor_set(v___x_298_, 1, v___x_295_);
v___x_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_299_, 0, v___x_295_);
lean_ctor_set(v___x_299_, 1, v___x_296_);
lean_ctor_set(v___x_299_, 2, v___x_297_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
lean_ctor_set(v___x_299_, 4, v___x_295_);
v_pos_300_ = lean_ctor_get(v_s_292_, 2);
lean_inc(v_pos_300_);
lean_dec_ref(v_s_292_);
v___x_301_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_301_, 0, v___x_299_);
v___x_302_ = l_Lean_Parser_ParserState_setPos(v___x_288_, v_pos_300_);
lean_inc_ref(v_ictx_252_);
v___x_303_ = l_Lean_Parser_ParserFn_run(v___x_301_, v_ictx_252_, v_pmctx_286_, v___x_291_, v___x_302_);
v___y_263_ = v___x_303_;
goto v___jp_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_toApplicative_310_ = _args[0];
lean_object* v_text_311_ = _args[1];
lean_object* v_logMessage_312_ = _args[2];
lean_object* v_toBind_313_ = _args[3];
lean_object* v_getFileName_314_ = _args[4];
lean_object* v_inst_315_ = _args[5];
lean_object* v___f_316_ = _args[6];
lean_object* v_ictx_317_ = _args[7];
lean_object* v_source_318_ = _args[8];
lean_object* v___f_319_ = _args[9];
lean_object* v_env_320_ = _args[10];
lean_object* v_____do__lift_321_ = _args[11];
lean_object* v_____do__lift_322_ = _args[12];
lean_object* v_val_323_ = _args[13];
lean_object* v___y_324_ = _args[14];
lean_object* v___x_325_ = _args[15];
lean_object* v_____do__lift_326_ = _args[16];
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_parseVersoDocString___redArg___lam__6(v_toApplicative_310_, v_text_311_, v_logMessage_312_, v_toBind_313_, v_getFileName_314_, v_inst_315_, v___f_316_, v_ictx_317_, v_source_318_, v___f_319_, v_env_320_, v_____do__lift_321_, v_____do__lift_322_, v_val_323_, v___y_324_, v___x_325_, v_____do__lift_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_toApplicative_328_, lean_object* v_text_329_, lean_object* v_logMessage_330_, lean_object* v_toBind_331_, lean_object* v_getFileName_332_, lean_object* v_inst_333_, lean_object* v___f_334_, lean_object* v_ictx_335_, lean_object* v_source_336_, lean_object* v___f_337_, lean_object* v_env_338_, lean_object* v_____do__lift_339_, lean_object* v_val_340_, lean_object* v___y_341_, lean_object* v___x_342_, lean_object* v_getOpenDecls_343_, lean_object* v_____do__lift_344_){
_start:
{
lean_object* v___f_345_; lean_object* v___x_346_; 
lean_inc(v_toBind_331_);
v___f_345_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_345_, 0, v_toApplicative_328_);
lean_closure_set(v___f_345_, 1, v_text_329_);
lean_closure_set(v___f_345_, 2, v_logMessage_330_);
lean_closure_set(v___f_345_, 3, v_toBind_331_);
lean_closure_set(v___f_345_, 4, v_getFileName_332_);
lean_closure_set(v___f_345_, 5, v_inst_333_);
lean_closure_set(v___f_345_, 6, v___f_334_);
lean_closure_set(v___f_345_, 7, v_ictx_335_);
lean_closure_set(v___f_345_, 8, v_source_336_);
lean_closure_set(v___f_345_, 9, v___f_337_);
lean_closure_set(v___f_345_, 10, v_env_338_);
lean_closure_set(v___f_345_, 11, v_____do__lift_339_);
lean_closure_set(v___f_345_, 12, v_____do__lift_344_);
lean_closure_set(v___f_345_, 13, v_val_340_);
lean_closure_set(v___f_345_, 14, v___y_341_);
lean_closure_set(v___f_345_, 15, v___x_342_);
v___x_346_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v_getOpenDecls_343_, v___f_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_toApplicative_347_ = _args[0];
lean_object* v_text_348_ = _args[1];
lean_object* v_logMessage_349_ = _args[2];
lean_object* v_toBind_350_ = _args[3];
lean_object* v_getFileName_351_ = _args[4];
lean_object* v_inst_352_ = _args[5];
lean_object* v___f_353_ = _args[6];
lean_object* v_ictx_354_ = _args[7];
lean_object* v_source_355_ = _args[8];
lean_object* v___f_356_ = _args[9];
lean_object* v_env_357_ = _args[10];
lean_object* v_____do__lift_358_ = _args[11];
lean_object* v_val_359_ = _args[12];
lean_object* v___y_360_ = _args[13];
lean_object* v___x_361_ = _args[14];
lean_object* v_getOpenDecls_362_ = _args[15];
lean_object* v_____do__lift_363_ = _args[16];
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_parseVersoDocString___redArg___lam__7(v_toApplicative_347_, v_text_348_, v_logMessage_349_, v_toBind_350_, v_getFileName_351_, v_inst_352_, v___f_353_, v_ictx_354_, v_source_355_, v___f_356_, v_env_357_, v_____do__lift_358_, v_val_359_, v___y_360_, v___x_361_, v_getOpenDecls_362_, v_____do__lift_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_inst_365_, lean_object* v_toApplicative_366_, lean_object* v_text_367_, lean_object* v_logMessage_368_, lean_object* v_toBind_369_, lean_object* v_getFileName_370_, lean_object* v_inst_371_, lean_object* v___f_372_, lean_object* v_ictx_373_, lean_object* v_source_374_, lean_object* v___f_375_, lean_object* v_env_376_, lean_object* v_val_377_, lean_object* v___y_378_, lean_object* v___x_379_, lean_object* v_____do__lift_380_){
_start:
{
lean_object* v_getCurrNamespace_381_; lean_object* v_getOpenDecls_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
v_getCurrNamespace_381_ = lean_ctor_get(v_inst_365_, 0);
lean_inc(v_getCurrNamespace_381_);
v_getOpenDecls_382_ = lean_ctor_get(v_inst_365_, 1);
lean_inc(v_getOpenDecls_382_);
lean_dec_ref(v_inst_365_);
lean_inc(v_toBind_369_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_383_, 0, v_toApplicative_366_);
lean_closure_set(v___f_383_, 1, v_text_367_);
lean_closure_set(v___f_383_, 2, v_logMessage_368_);
lean_closure_set(v___f_383_, 3, v_toBind_369_);
lean_closure_set(v___f_383_, 4, v_getFileName_370_);
lean_closure_set(v___f_383_, 5, v_inst_371_);
lean_closure_set(v___f_383_, 6, v___f_372_);
lean_closure_set(v___f_383_, 7, v_ictx_373_);
lean_closure_set(v___f_383_, 8, v_source_374_);
lean_closure_set(v___f_383_, 9, v___f_375_);
lean_closure_set(v___f_383_, 10, v_env_376_);
lean_closure_set(v___f_383_, 11, v_____do__lift_380_);
lean_closure_set(v___f_383_, 12, v_val_377_);
lean_closure_set(v___f_383_, 13, v___y_378_);
lean_closure_set(v___f_383_, 14, v___x_379_);
lean_closure_set(v___f_383_, 15, v_getOpenDecls_382_);
v___x_384_ = lean_apply_4(v_toBind_369_, lean_box(0), lean_box(0), v_getCurrNamespace_381_, v___f_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_source_385_, lean_object* v_text_386_, lean_object* v___y_387_, lean_object* v_inst_388_, lean_object* v_toApplicative_389_, lean_object* v_logMessage_390_, lean_object* v_toBind_391_, lean_object* v_getFileName_392_, lean_object* v_inst_393_, lean_object* v___f_394_, lean_object* v___f_395_, lean_object* v_env_396_, lean_object* v_val_397_, lean_object* v___x_398_, lean_object* v_inst_399_, lean_object* v_____do__lift_400_){
_start:
{
lean_object* v_ictx_401_; lean_object* v___f_402_; lean_object* v___x_403_; 
lean_inc(v___y_387_);
lean_inc_ref(v_text_386_);
lean_inc_ref(v_source_385_);
v_ictx_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_401_, 0, v_source_385_);
lean_ctor_set(v_ictx_401_, 1, v_____do__lift_400_);
lean_ctor_set(v_ictx_401_, 2, v_text_386_);
lean_ctor_set(v_ictx_401_, 3, v___y_387_);
lean_inc(v_toBind_391_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(v___f_402_, 0, v_inst_388_);
lean_closure_set(v___f_402_, 1, v_toApplicative_389_);
lean_closure_set(v___f_402_, 2, v_text_386_);
lean_closure_set(v___f_402_, 3, v_logMessage_390_);
lean_closure_set(v___f_402_, 4, v_toBind_391_);
lean_closure_set(v___f_402_, 5, v_getFileName_392_);
lean_closure_set(v___f_402_, 6, v_inst_393_);
lean_closure_set(v___f_402_, 7, v___f_394_);
lean_closure_set(v___f_402_, 8, v_ictx_401_);
lean_closure_set(v___f_402_, 9, v_source_385_);
lean_closure_set(v___f_402_, 10, v___f_395_);
lean_closure_set(v___f_402_, 11, v_env_396_);
lean_closure_set(v___f_402_, 12, v_val_397_);
lean_closure_set(v___f_402_, 13, v___y_387_);
lean_closure_set(v___f_402_, 14, v___x_398_);
v___x_403_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v_inst_399_, v___f_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_inst_404_, lean_object* v_source_405_, lean_object* v_text_406_, lean_object* v___y_407_, lean_object* v_inst_408_, lean_object* v_toApplicative_409_, lean_object* v_toBind_410_, lean_object* v_inst_411_, lean_object* v___f_412_, lean_object* v___f_413_, lean_object* v_val_414_, lean_object* v___x_415_, lean_object* v_inst_416_, lean_object* v_env_417_){
_start:
{
lean_object* v_getFileName_418_; lean_object* v_logMessage_419_; lean_object* v___f_420_; lean_object* v___x_421_; 
v_getFileName_418_ = lean_ctor_get(v_inst_404_, 2);
lean_inc(v_getFileName_418_);
v_logMessage_419_ = lean_ctor_get(v_inst_404_, 4);
lean_inc(v_logMessage_419_);
lean_dec_ref(v_inst_404_);
lean_inc(v_getFileName_418_);
lean_inc(v_toBind_410_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 16, 15);
lean_closure_set(v___f_420_, 0, v_source_405_);
lean_closure_set(v___f_420_, 1, v_text_406_);
lean_closure_set(v___f_420_, 2, v___y_407_);
lean_closure_set(v___f_420_, 3, v_inst_408_);
lean_closure_set(v___f_420_, 4, v_toApplicative_409_);
lean_closure_set(v___f_420_, 5, v_logMessage_419_);
lean_closure_set(v___f_420_, 6, v_toBind_410_);
lean_closure_set(v___f_420_, 7, v_getFileName_418_);
lean_closure_set(v___f_420_, 8, v_inst_411_);
lean_closure_set(v___f_420_, 9, v___f_412_);
lean_closure_set(v___f_420_, 10, v___f_413_);
lean_closure_set(v___f_420_, 11, v_env_417_);
lean_closure_set(v___f_420_, 12, v_val_414_);
lean_closure_set(v___f_420_, 13, v___x_415_);
lean_closure_set(v___f_420_, 14, v_inst_416_);
v___x_421_ = lean_apply_4(v_toBind_410_, lean_box(0), lean_box(0), v_getFileName_418_, v___f_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__11___closed__0));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* v_docComment_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_toApplicative_429_, lean_object* v_toBind_430_, lean_object* v_inst_431_, lean_object* v___f_432_, lean_object* v___f_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_text_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_unsigned_to_nat(1u);
v___x_438_ = l_Lean_Syntax_getArg(v_docComment_425_, v___x_437_);
v___x_439_ = 1;
v___x_440_ = l_Lean_Syntax_getPos_x3f(v___x_438_, v___x_439_);
if (lean_obj_tag(v___x_440_) == 1)
{
lean_object* v_val_441_; lean_object* v___x_442_; 
v_val_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_val_441_);
lean_dec_ref(v___x_440_);
v___x_442_ = l_Lean_Syntax_getTailPos_x3f(v___x_438_, v___x_439_);
lean_dec(v___x_438_);
if (lean_obj_tag(v___x_442_) == 1)
{
lean_object* v_val_443_; lean_object* v_source_444_; lean_object* v___y_446_; lean_object* v___x_450_; lean_object* v_endPos_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
lean_dec_ref(v_inst_435_);
lean_dec(v_docComment_425_);
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref(v___x_442_);
v_source_444_ = lean_ctor_get(v_text_436_, 0);
lean_inc_ref(v_source_444_);
v___x_450_ = lean_string_utf8_prev(v_source_444_, v_val_443_);
lean_dec(v_val_443_);
v_endPos_451_ = lean_string_utf8_prev(v_source_444_, v___x_450_);
lean_dec(v___x_450_);
v___x_452_ = lean_string_utf8_byte_size(v_source_444_);
v___x_453_ = lean_nat_dec_le(v_endPos_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_dec(v_endPos_451_);
v___y_446_ = v___x_452_;
goto v___jp_445_;
}
else
{
v___y_446_ = v_endPos_451_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v_getEnv_447_; lean_object* v___f_448_; lean_object* v___x_449_; 
v_getEnv_447_ = lean_ctor_get(v_inst_426_, 0);
lean_inc(v_getEnv_447_);
lean_dec_ref(v_inst_426_);
lean_inc(v_toBind_430_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 14, 13);
lean_closure_set(v___f_448_, 0, v_inst_427_);
lean_closure_set(v___f_448_, 1, v_source_444_);
lean_closure_set(v___f_448_, 2, v_text_436_);
lean_closure_set(v___f_448_, 3, v___y_446_);
lean_closure_set(v___f_448_, 4, v_inst_428_);
lean_closure_set(v___f_448_, 5, v_toApplicative_429_);
lean_closure_set(v___f_448_, 6, v_toBind_430_);
lean_closure_set(v___f_448_, 7, v_inst_431_);
lean_closure_set(v___f_448_, 8, v___f_432_);
lean_closure_set(v___f_448_, 9, v___f_433_);
lean_closure_set(v___f_448_, 10, v_val_441_);
lean_closure_set(v___f_448_, 11, v___x_437_);
lean_closure_set(v___f_448_, 12, v_inst_434_);
v___x_449_ = lean_apply_4(v_toBind_430_, lean_box(0), lean_box(0), v_getEnv_447_, v___f_448_);
return v___x_449_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v___x_442_);
lean_dec(v_val_441_);
lean_dec_ref(v_text_436_);
lean_dec(v_inst_434_);
lean_dec(v___f_433_);
lean_dec(v___f_432_);
lean_dec(v_toBind_430_);
lean_dec_ref(v_toApplicative_429_);
lean_dec_ref(v_inst_428_);
lean_dec_ref(v_inst_427_);
lean_dec_ref(v_inst_426_);
v___x_454_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_455_ = l_Lean_throwErrorAt___redArg(v_inst_431_, v_inst_435_, v_docComment_425_, v___x_454_);
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_440_);
lean_dec(v___x_438_);
lean_dec_ref(v_text_436_);
lean_dec(v_inst_434_);
lean_dec(v___f_433_);
lean_dec(v___f_432_);
lean_dec(v_toBind_430_);
lean_dec_ref(v_toApplicative_429_);
lean_dec_ref(v_inst_428_);
lean_dec_ref(v_inst_427_);
lean_dec_ref(v_inst_426_);
v___x_456_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_457_ = l_Lean_throwErrorAt___redArg(v_inst_431_, v_inst_435_, v_docComment_425_, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_docComment_475_){
_start:
{
lean_object* v_toApplicative_476_; lean_object* v_toBind_477_; lean_object* v___f_478_; lean_object* v___f_479_; lean_object* v___f_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_toApplicative_476_ = lean_ctor_get(v_inst_468_, 0);
lean_inc_ref(v_toApplicative_476_);
v_toBind_477_ = lean_ctor_get(v_inst_468_, 1);
lean_inc(v_toBind_477_);
lean_inc_ref(v_toApplicative_476_);
v___f_478_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_478_, 0, v_toApplicative_476_);
lean_inc_ref(v_toApplicative_476_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_479_, 0, v_toApplicative_476_);
lean_inc(v_toBind_477_);
lean_inc_ref(v_toApplicative_476_);
lean_inc(v_docComment_475_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 12, 11);
lean_closure_set(v___f_480_, 0, v_docComment_475_);
lean_closure_set(v___f_480_, 1, v_inst_471_);
lean_closure_set(v___f_480_, 2, v_inst_473_);
lean_closure_set(v___f_480_, 3, v_inst_474_);
lean_closure_set(v___f_480_, 4, v_toApplicative_476_);
lean_closure_set(v___f_480_, 5, v_toBind_477_);
lean_closure_set(v___f_480_, 6, v_inst_468_);
lean_closure_set(v___f_480_, 7, v___f_478_);
lean_closure_set(v___f_480_, 8, v___f_479_);
lean_closure_set(v___f_480_, 9, v_inst_472_);
lean_closure_set(v___f_480_, 10, v_inst_470_);
lean_inc(v_docComment_475_);
v___x_481_ = l_Lean_Syntax_getKind(v_docComment_475_);
v___x_482_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_483_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_484_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_485_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_486_ = lean_name_eq(v___x_481_, v___x_485_);
lean_dec(v___x_481_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
lean_dec_ref(v_toApplicative_476_);
lean_dec(v_docComment_475_);
v___x_487_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l_Lean_Syntax_getArg(v_docComment_475_, v___x_488_);
lean_dec(v_docComment_475_);
if (lean_obj_tag(v___x_489_) == 1)
{
lean_object* v_kind_490_; 
v_kind_490_ = lean_ctor_get(v___x_489_, 1);
lean_inc(v_kind_490_);
if (lean_obj_tag(v_kind_490_) == 1)
{
lean_object* v_pre_491_; 
v_pre_491_ = lean_ctor_get(v_kind_490_, 0);
lean_inc(v_pre_491_);
if (lean_obj_tag(v_pre_491_) == 1)
{
lean_object* v_pre_492_; 
v_pre_492_ = lean_ctor_get(v_pre_491_, 0);
lean_inc(v_pre_492_);
if (lean_obj_tag(v_pre_492_) == 1)
{
lean_object* v_pre_493_; 
v_pre_493_ = lean_ctor_get(v_pre_492_, 0);
lean_inc(v_pre_493_);
if (lean_obj_tag(v_pre_493_) == 1)
{
lean_object* v_pre_494_; 
v_pre_494_ = lean_ctor_get(v_pre_493_, 0);
lean_inc(v_pre_494_);
if (lean_obj_tag(v_pre_494_) == 0)
{
lean_object* v_info_495_; lean_object* v_args_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_528_; 
v_info_495_ = lean_ctor_get(v___x_489_, 0);
v_args_496_ = lean_ctor_get(v___x_489_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v___x_489_, 1);
lean_dec(v_unused_529_);
v___x_498_ = v___x_489_;
v_isShared_499_ = v_isSharedCheck_528_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_args_496_);
lean_inc(v_info_495_);
lean_dec(v___x_489_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_528_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_str_500_; lean_object* v_str_501_; lean_object* v_str_502_; lean_object* v_str_503_; uint8_t v___x_504_; 
v_str_500_ = lean_ctor_get(v_kind_490_, 1);
lean_inc_ref(v_str_500_);
lean_dec_ref(v_kind_490_);
v_str_501_ = lean_ctor_get(v_pre_491_, 1);
lean_inc_ref(v_str_501_);
lean_dec_ref(v_pre_491_);
v_str_502_ = lean_ctor_get(v_pre_492_, 1);
lean_inc_ref(v_str_502_);
lean_dec_ref(v_pre_492_);
v_str_503_ = lean_ctor_get(v_pre_493_, 1);
lean_inc_ref(v_str_503_);
lean_dec_ref(v_pre_493_);
v___x_504_ = lean_string_dec_eq(v_str_503_, v___x_482_);
lean_dec_ref(v_str_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_str_502_);
lean_dec_ref(v_str_501_);
lean_dec_ref(v_str_500_);
lean_del_object(v___x_498_);
lean_dec_ref(v_args_496_);
lean_dec(v_info_495_);
lean_dec_ref(v_toApplicative_476_);
v___x_505_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_505_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_string_dec_eq(v_str_502_, v___x_483_);
lean_dec_ref(v_str_502_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v_str_501_);
lean_dec_ref(v_str_500_);
lean_del_object(v___x_498_);
lean_dec_ref(v_args_496_);
lean_dec(v_info_495_);
lean_dec_ref(v_toApplicative_476_);
v___x_507_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_507_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = lean_string_dec_eq(v_str_501_, v___x_484_);
lean_dec_ref(v_str_501_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_str_500_);
lean_del_object(v___x_498_);
lean_dec_ref(v_args_496_);
lean_dec(v_info_495_);
lean_dec_ref(v_toApplicative_476_);
v___x_509_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_511_ = lean_string_dec_eq(v_str_500_, v___x_510_);
lean_dec_ref(v_str_500_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; 
lean_del_object(v___x_498_);
lean_dec_ref(v_args_496_);
lean_dec(v_info_495_);
lean_dec_ref(v_toApplicative_476_);
v___x_512_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_512_;
}
else
{
lean_dec_ref(v___f_480_);
lean_dec(v_toBind_477_);
lean_dec(v_inst_469_);
if (v___x_511_ == 0)
{
lean_object* v_toPure_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_del_object(v___x_498_);
lean_dec_ref(v_args_496_);
lean_dec(v_info_495_);
v_toPure_513_ = lean_ctor_get(v_toApplicative_476_, 1);
lean_inc(v_toPure_513_);
lean_dec_ref(v_toApplicative_476_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_2(v_toPure_513_, lean_box(0), v___x_514_);
return v___x_515_;
}
else
{
lean_object* v_toPure_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v_toPure_516_ = lean_ctor_get(v_toApplicative_476_, 1);
lean_inc(v_toPure_516_);
lean_dec_ref(v_toApplicative_476_);
v___x_517_ = l_Lean_Name_str___override(v_pre_494_, v___x_482_);
v___x_518_ = l_Lean_Name_str___override(v___x_517_, v___x_483_);
v___x_519_ = l_Lean_Name_str___override(v___x_518_, v___x_484_);
v___x_520_ = l_Lean_Name_str___override(v___x_519_, v___x_510_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_520_);
v___x_522_ = v___x_498_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_info_495_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_args_496_);
v___x_522_ = v_reuseFailAlloc_527_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = l_Lean_Syntax_getArg(v___x_522_, v___x_523_);
lean_dec_ref(v___x_522_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = lean_apply_2(v_toPure_516_, lean_box(0), v___x_525_);
return v___x_526_;
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
lean_object* v___x_530_; 
lean_dec(v_pre_494_);
lean_dec_ref(v_pre_493_);
lean_dec_ref(v_pre_492_);
lean_dec_ref(v_pre_491_);
lean_dec_ref(v_kind_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v_toApplicative_476_);
v___x_530_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; 
lean_dec_ref(v_pre_492_);
lean_dec(v_pre_493_);
lean_dec_ref(v_pre_491_);
lean_dec_ref(v_kind_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v_toApplicative_476_);
v___x_531_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v_pre_491_);
lean_dec(v_pre_492_);
lean_dec_ref(v_kind_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v_toApplicative_476_);
v___x_532_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; 
lean_dec(v_pre_491_);
lean_dec_ref(v_kind_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v_toApplicative_476_);
v___x_533_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_533_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec_ref(v___x_489_);
lean_dec(v_kind_490_);
lean_dec_ref(v_toApplicative_476_);
v___x_534_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; 
lean_dec(v___x_489_);
lean_dec_ref(v_toApplicative_476_);
v___x_535_ = lean_apply_4(v_toBind_477_, lean_box(0), lean_box(0), v_inst_469_, v___f_480_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_docComment_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_parseVersoDocString___redArg(v_inst_537_, v_inst_538_, v_inst_539_, v_inst_540_, v_inst_541_, v_inst_542_, v_inst_543_, v_docComment_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v___y_546_, lean_object* v_text_547_, lean_object* v_source_548_, lean_object* v_logMessage_549_, lean_object* v_____do__lift_550_){
_start:
{
lean_object* v_pos_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint32_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v_pos_551_ = lean_ctor_get(v___y_546_, 2);
v___x_552_ = l_Lean_FileMap_toPosition(v_text_547_, v_pos_551_);
v___x_553_ = lean_box(0);
v___x_554_ = 0;
v___x_555_ = 2;
v___x_556_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_557_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_558_ = lean_string_utf8_get(v_source_548_, v_pos_551_);
v___x_559_ = lean_string_push(v___x_556_, v___x_558_);
v___x_560_ = lean_string_append(v___x_557_, v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
v___x_563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
v___x_564_ = l_Lean_MessageData_ofFormat(v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_565_, 0, v_____do__lift_550_);
lean_ctor_set(v___x_565_, 1, v___x_552_);
lean_ctor_set(v___x_565_, 2, v___x_553_);
lean_ctor_set(v___x_565_, 3, v___x_556_);
lean_ctor_set(v___x_565_, 4, v___x_564_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*5, v___x_554_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*5 + 1, v___x_555_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*5 + 2, v___x_554_);
v___x_566_ = lean_apply_1(v_logMessage_549_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v___y_567_, lean_object* v_text_568_, lean_object* v_source_569_, lean_object* v_logMessage_570_, lean_object* v_____do__lift_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v___y_567_, v_text_568_, v_source_569_, v_logMessage_570_, v_____do__lift_571_);
lean_dec_ref(v_source_569_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v___x_573_, lean_object* v_toPure_574_, lean_object* v_____r_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
v___x_577_ = lean_apply_2(v_toPure_574_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v_text_578_, lean_object* v_fst_579_, lean_object* v_snd_580_, lean_object* v_logMessage_581_, lean_object* v_toBind_582_, lean_object* v___f_583_, lean_object* v_____do__lift_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_585_ = l_Lean_FileMap_toPosition(v_text_578_, v_fst_579_);
v___x_586_ = lean_box(0);
v___x_587_ = 0;
v___x_588_ = 2;
v___x_589_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_590_ = l_Lean_Parser_Error_toString(v_snd_580_);
v___x_591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
v___x_592_ = l_Lean_MessageData_ofFormat(v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_593_, 0, v_____do__lift_584_);
lean_ctor_set(v___x_593_, 1, v___x_585_);
lean_ctor_set(v___x_593_, 2, v___x_586_);
lean_ctor_set(v___x_593_, 3, v___x_589_);
lean_ctor_set(v___x_593_, 4, v___x_592_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*5, v___x_587_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*5 + 1, v___x_588_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*5 + 2, v___x_587_);
v___x_594_ = lean_apply_1(v_logMessage_581_, v___x_593_);
v___x_595_ = lean_apply_4(v_toBind_582_, lean_box(0), lean_box(0), v___x_594_, v___f_583_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2___boxed(lean_object* v_text_596_, lean_object* v_fst_597_, lean_object* v_snd_598_, lean_object* v_logMessage_599_, lean_object* v_toBind_600_, lean_object* v___f_601_, lean_object* v_____do__lift_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_reportVersoParseFailure___redArg___lam__2(v_text_596_, v_fst_597_, v_snd_598_, v_logMessage_599_, v_toBind_600_, v___f_601_, v_____do__lift_602_);
lean_dec(v_fst_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_text_604_, lean_object* v_logMessage_605_, lean_object* v_toBind_606_, lean_object* v___f_607_, lean_object* v_getFileName_608_, lean_object* v_a_609_, lean_object* v_x_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_snd_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___f_615_; lean_object* v___x_616_; 
v_snd_612_ = lean_ctor_get(v_a_609_, 1);
lean_inc(v_snd_612_);
v_fst_613_ = lean_ctor_get(v_a_609_, 0);
lean_inc(v_fst_613_);
lean_dec_ref(v_a_609_);
v_snd_614_ = lean_ctor_get(v_snd_612_, 1);
lean_inc(v_snd_614_);
lean_dec(v_snd_612_);
lean_inc(v_toBind_606_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_615_, 0, v_text_604_);
lean_closure_set(v___f_615_, 1, v_fst_613_);
lean_closure_set(v___f_615_, 2, v_snd_614_);
lean_closure_set(v___f_615_, 3, v_logMessage_605_);
lean_closure_set(v___f_615_, 4, v_toBind_606_);
lean_closure_set(v___f_615_, 5, v___f_607_);
v___x_616_ = lean_apply_4(v_toBind_606_, lean_box(0), lean_box(0), v_getFileName_608_, v___f_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_toPure_617_, lean_object* v___x_618_, lean_object* v_toBind_619_, lean_object* v_getFileName_620_, lean_object* v___f_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v___y_624_, lean_object* v_ictx_625_, lean_object* v_____s_626_){
_start:
{
uint8_t v___y_628_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_array_get_size(v___x_622_);
v___x_632_ = lean_nat_dec_eq(v___x_631_, v___x_623_);
if (v___x_632_ == 0)
{
v___y_628_ = v___x_632_;
goto v___jp_627_;
}
else
{
lean_object* v_pos_633_; uint8_t v___x_634_; 
v_pos_633_ = lean_ctor_get(v___y_624_, 2);
v___x_634_ = l_Lean_Parser_InputContext_atEnd(v_ictx_625_, v_pos_633_);
if (v___x_634_ == 0)
{
v___y_628_ = v___x_632_;
goto v___jp_627_;
}
else
{
lean_object* v___x_635_; 
lean_dec(v___f_621_);
lean_dec(v_getFileName_620_);
lean_dec(v_toBind_619_);
v___x_635_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_618_);
return v___x_635_;
}
}
v___jp_627_:
{
if (v___y_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v___f_621_);
lean_dec(v_getFileName_620_);
lean_dec(v_toBind_619_);
v___x_629_ = lean_apply_2(v_toPure_617_, lean_box(0), v___x_618_);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
lean_dec(v_toPure_617_);
v___x_630_ = lean_apply_4(v_toBind_619_, lean_box(0), lean_box(0), v_getFileName_620_, v___f_621_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object* v_toPure_636_, lean_object* v___x_637_, lean_object* v_toBind_638_, lean_object* v_getFileName_639_, lean_object* v___f_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___y_643_, lean_object* v_ictx_644_, lean_object* v_____s_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_reportVersoParseFailure___redArg___lam__4(v_toPure_636_, v___x_637_, v_toBind_638_, v_getFileName_639_, v___f_640_, v___x_641_, v___x_642_, v___y_643_, v_ictx_644_, v_____s_645_);
lean_dec_ref(v_ictx_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_text_647_, lean_object* v_source_648_, lean_object* v_logMessage_649_, lean_object* v_toPure_650_, lean_object* v_toBind_651_, lean_object* v_getFileName_652_, lean_object* v___x_653_, lean_object* v_ictx_654_, lean_object* v_inst_655_, lean_object* v_env_656_, lean_object* v_____do__lift_657_, lean_object* v_____do__lift_658_, lean_object* v_val_659_, lean_object* v___y_660_, lean_object* v_____do__lift_661_){
_start:
{
lean_object* v___y_663_; lean_object* v_pmctx_674_; lean_object* v_blockCtxt_675_; lean_object* v___x_676_; lean_object* v_s_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v_s_680_; uint8_t v___y_682_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
lean_inc_ref(v_env_656_);
v_pmctx_674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_674_, 0, v_env_656_);
lean_ctor_set(v_pmctx_674_, 1, v_____do__lift_657_);
lean_ctor_set(v_pmctx_674_, 2, v_____do__lift_658_);
lean_ctor_set(v_pmctx_674_, 3, v_____do__lift_661_);
lean_inc(v_val_659_);
lean_inc_ref(v_text_647_);
v_blockCtxt_675_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_647_, v_val_659_, v___y_660_);
v___x_676_ = l_Lean_Parser_mkParserState(v_source_648_);
lean_inc_ref(v___x_676_);
v_s_677_ = l_Lean_Parser_ParserState_setPos(v___x_676_, v_val_659_);
v___x_678_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_678_, 0, v_blockCtxt_675_);
v___x_679_ = l_Lean_Parser_getTokenTable(v_env_656_);
lean_inc_ref(v___x_679_);
lean_inc_ref(v_pmctx_674_);
lean_inc_ref(v_ictx_654_);
v_s_680_ = l_Lean_Parser_ParserFn_run(v___x_678_, v_ictx_654_, v_pmctx_674_, v___x_679_, v_s_677_);
lean_inc_ref(v_s_680_);
v___x_692_ = l_Lean_Parser_ParserState_allErrors(v_s_680_);
v___x_693_ = lean_array_get_size(v___x_692_);
lean_dec_ref(v___x_692_);
v___x_694_ = lean_nat_dec_eq(v___x_693_, v___x_653_);
if (v___x_694_ == 0)
{
v___y_682_ = v___x_694_;
goto v___jp_681_;
}
else
{
lean_object* v_pos_695_; uint8_t v___x_696_; 
v_pos_695_ = lean_ctor_get(v_s_680_, 2);
lean_inc(v_pos_695_);
v___x_696_ = l_Lean_Parser_InputContext_atEnd(v_ictx_654_, v_pos_695_);
lean_dec(v_pos_695_);
if (v___x_696_ == 0)
{
v___y_682_ = v___x_694_;
goto v___jp_681_;
}
else
{
lean_dec_ref(v___x_679_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v_pmctx_674_);
v___y_663_ = v_s_680_;
goto v___jp_662_;
}
}
v___jp_662_:
{
lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___f_669_; size_t v_sz_670_; size_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
lean_inc(v_logMessage_649_);
lean_inc_ref(v_text_647_);
lean_inc_ref(v___y_663_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_664_, 0, v___y_663_);
lean_closure_set(v___f_664_, 1, v_text_647_);
lean_closure_set(v___f_664_, 2, v_source_648_);
lean_closure_set(v___f_664_, 3, v_logMessage_649_);
lean_inc_ref(v___y_663_);
v___x_665_ = l_Lean_Parser_ParserState_allErrors(v___y_663_);
v___x_666_ = lean_box(0);
lean_inc(v_toPure_650_);
v___f_667_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1), 3, 2);
lean_closure_set(v___f_667_, 0, v___x_666_);
lean_closure_set(v___f_667_, 1, v_toPure_650_);
lean_inc(v_getFileName_652_);
lean_inc(v_toBind_651_);
v___f_668_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 8, 5);
lean_closure_set(v___f_668_, 0, v_text_647_);
lean_closure_set(v___f_668_, 1, v_logMessage_649_);
lean_closure_set(v___f_668_, 2, v_toBind_651_);
lean_closure_set(v___f_668_, 3, v___f_667_);
lean_closure_set(v___f_668_, 4, v_getFileName_652_);
lean_inc_ref(v___x_665_);
lean_inc(v_toBind_651_);
v___f_669_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_669_, 0, v_toPure_650_);
lean_closure_set(v___f_669_, 1, v___x_666_);
lean_closure_set(v___f_669_, 2, v_toBind_651_);
lean_closure_set(v___f_669_, 3, v_getFileName_652_);
lean_closure_set(v___f_669_, 4, v___f_664_);
lean_closure_set(v___f_669_, 5, v___x_665_);
lean_closure_set(v___f_669_, 6, v___x_653_);
lean_closure_set(v___f_669_, 7, v___y_663_);
lean_closure_set(v___f_669_, 8, v_ictx_654_);
v_sz_670_ = lean_array_size(v___x_665_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___x_665_, v___f_668_, v_sz_670_, v___x_671_, v___x_666_);
v___x_673_ = lean_apply_4(v_toBind_651_, lean_box(0), lean_box(0), v___x_672_, v___f_669_);
return v___x_673_;
}
v___jp_681_:
{
if (v___y_682_ == 0)
{
lean_dec_ref(v___x_679_);
lean_dec_ref(v___x_676_);
lean_dec_ref(v_pmctx_674_);
v___y_663_ = v_s_680_;
goto v___jp_662_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_pos_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_box(0);
v___x_685_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_653_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_653_);
lean_inc_n(v___x_653_, 2);
v___x_687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_687_, 0, v___x_653_);
lean_ctor_set(v___x_687_, 1, v___x_683_);
lean_ctor_set(v___x_687_, 2, v___x_684_);
lean_ctor_set(v___x_687_, 3, v___x_686_);
lean_ctor_set(v___x_687_, 4, v___x_653_);
v_pos_688_ = lean_ctor_get(v_s_680_, 2);
lean_inc(v_pos_688_);
lean_dec_ref(v_s_680_);
v___x_689_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_689_, 0, v___x_687_);
v___x_690_ = l_Lean_Parser_ParserState_setPos(v___x_676_, v_pos_688_);
lean_inc_ref(v_ictx_654_);
v___x_691_ = l_Lean_Parser_ParserFn_run(v___x_689_, v_ictx_654_, v_pmctx_674_, v___x_679_, v___x_690_);
v___y_663_ = v___x_691_;
goto v___jp_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_text_697_, lean_object* v_source_698_, lean_object* v_logMessage_699_, lean_object* v_toPure_700_, lean_object* v_toBind_701_, lean_object* v_getFileName_702_, lean_object* v___x_703_, lean_object* v_ictx_704_, lean_object* v_inst_705_, lean_object* v_env_706_, lean_object* v_____do__lift_707_, lean_object* v_val_708_, lean_object* v___y_709_, lean_object* v_getOpenDecls_710_, lean_object* v_____do__lift_711_){
_start:
{
lean_object* v___f_712_; lean_object* v___x_713_; 
lean_inc(v_toBind_701_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(v___f_712_, 0, v_text_697_);
lean_closure_set(v___f_712_, 1, v_source_698_);
lean_closure_set(v___f_712_, 2, v_logMessage_699_);
lean_closure_set(v___f_712_, 3, v_toPure_700_);
lean_closure_set(v___f_712_, 4, v_toBind_701_);
lean_closure_set(v___f_712_, 5, v_getFileName_702_);
lean_closure_set(v___f_712_, 6, v___x_703_);
lean_closure_set(v___f_712_, 7, v_ictx_704_);
lean_closure_set(v___f_712_, 8, v_inst_705_);
lean_closure_set(v___f_712_, 9, v_env_706_);
lean_closure_set(v___f_712_, 10, v_____do__lift_707_);
lean_closure_set(v___f_712_, 11, v_____do__lift_711_);
lean_closure_set(v___f_712_, 12, v_val_708_);
lean_closure_set(v___f_712_, 13, v___y_709_);
v___x_713_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v_getOpenDecls_710_, v___f_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_714_, lean_object* v_text_715_, lean_object* v_source_716_, lean_object* v_logMessage_717_, lean_object* v_toPure_718_, lean_object* v_toBind_719_, lean_object* v_getFileName_720_, lean_object* v___x_721_, lean_object* v_ictx_722_, lean_object* v_inst_723_, lean_object* v_env_724_, lean_object* v_val_725_, lean_object* v___y_726_, lean_object* v_____do__lift_727_){
_start:
{
lean_object* v_getCurrNamespace_728_; lean_object* v_getOpenDecls_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v_getCurrNamespace_728_ = lean_ctor_get(v_inst_714_, 0);
lean_inc(v_getCurrNamespace_728_);
v_getOpenDecls_729_ = lean_ctor_get(v_inst_714_, 1);
lean_inc(v_getOpenDecls_729_);
lean_dec_ref(v_inst_714_);
lean_inc(v_toBind_719_);
v___f_730_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 15, 14);
lean_closure_set(v___f_730_, 0, v_text_715_);
lean_closure_set(v___f_730_, 1, v_source_716_);
lean_closure_set(v___f_730_, 2, v_logMessage_717_);
lean_closure_set(v___f_730_, 3, v_toPure_718_);
lean_closure_set(v___f_730_, 4, v_toBind_719_);
lean_closure_set(v___f_730_, 5, v_getFileName_720_);
lean_closure_set(v___f_730_, 6, v___x_721_);
lean_closure_set(v___f_730_, 7, v_ictx_722_);
lean_closure_set(v___f_730_, 8, v_inst_723_);
lean_closure_set(v___f_730_, 9, v_env_724_);
lean_closure_set(v___f_730_, 10, v_____do__lift_727_);
lean_closure_set(v___f_730_, 11, v_val_725_);
lean_closure_set(v___f_730_, 12, v___y_726_);
lean_closure_set(v___f_730_, 13, v_getOpenDecls_729_);
v___x_731_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v_getCurrNamespace_728_, v___f_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_source_732_, lean_object* v_text_733_, lean_object* v___y_734_, lean_object* v_inst_735_, lean_object* v_logMessage_736_, lean_object* v_toPure_737_, lean_object* v_toBind_738_, lean_object* v_getFileName_739_, lean_object* v___x_740_, lean_object* v_inst_741_, lean_object* v_env_742_, lean_object* v_val_743_, lean_object* v_inst_744_, lean_object* v_____do__lift_745_){
_start:
{
lean_object* v_ictx_746_; lean_object* v___f_747_; lean_object* v___x_748_; 
lean_inc(v___y_734_);
lean_inc_ref(v_text_733_);
lean_inc_ref(v_source_732_);
v_ictx_746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_746_, 0, v_source_732_);
lean_ctor_set(v_ictx_746_, 1, v_____do__lift_745_);
lean_ctor_set(v_ictx_746_, 2, v_text_733_);
lean_ctor_set(v_ictx_746_, 3, v___y_734_);
lean_inc(v_toBind_738_);
v___f_747_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 14, 13);
lean_closure_set(v___f_747_, 0, v_inst_735_);
lean_closure_set(v___f_747_, 1, v_text_733_);
lean_closure_set(v___f_747_, 2, v_source_732_);
lean_closure_set(v___f_747_, 3, v_logMessage_736_);
lean_closure_set(v___f_747_, 4, v_toPure_737_);
lean_closure_set(v___f_747_, 5, v_toBind_738_);
lean_closure_set(v___f_747_, 6, v_getFileName_739_);
lean_closure_set(v___f_747_, 7, v___x_740_);
lean_closure_set(v___f_747_, 8, v_ictx_746_);
lean_closure_set(v___f_747_, 9, v_inst_741_);
lean_closure_set(v___f_747_, 10, v_env_742_);
lean_closure_set(v___f_747_, 11, v_val_743_);
lean_closure_set(v___f_747_, 12, v___y_734_);
v___x_748_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v_inst_744_, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object* v_inst_749_, lean_object* v_source_750_, lean_object* v_text_751_, lean_object* v___y_752_, lean_object* v_inst_753_, lean_object* v_toPure_754_, lean_object* v_toBind_755_, lean_object* v___x_756_, lean_object* v_inst_757_, lean_object* v_val_758_, lean_object* v_inst_759_, lean_object* v_env_760_){
_start:
{
lean_object* v_getFileName_761_; lean_object* v_logMessage_762_; lean_object* v___f_763_; lean_object* v___x_764_; 
v_getFileName_761_ = lean_ctor_get(v_inst_749_, 2);
lean_inc(v_getFileName_761_);
v_logMessage_762_ = lean_ctor_get(v_inst_749_, 4);
lean_inc(v_logMessage_762_);
lean_dec_ref(v_inst_749_);
lean_inc(v_getFileName_761_);
lean_inc(v_toBind_755_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 14, 13);
lean_closure_set(v___f_763_, 0, v_source_750_);
lean_closure_set(v___f_763_, 1, v_text_751_);
lean_closure_set(v___f_763_, 2, v___y_752_);
lean_closure_set(v___f_763_, 3, v_inst_753_);
lean_closure_set(v___f_763_, 4, v_logMessage_762_);
lean_closure_set(v___f_763_, 5, v_toPure_754_);
lean_closure_set(v___f_763_, 6, v_toBind_755_);
lean_closure_set(v___f_763_, 7, v_getFileName_761_);
lean_closure_set(v___f_763_, 8, v___x_756_);
lean_closure_set(v___f_763_, 9, v_inst_757_);
lean_closure_set(v___f_763_, 10, v_env_760_);
lean_closure_set(v___f_763_, 11, v_val_758_);
lean_closure_set(v___f_763_, 12, v_inst_759_);
v___x_764_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v_getFileName_761_, v___f_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_toPure_768_, lean_object* v_toBind_769_, lean_object* v___x_770_, lean_object* v_inst_771_, lean_object* v_val_772_, lean_object* v_inst_773_, lean_object* v_val_774_, lean_object* v_text_775_){
_start:
{
lean_object* v_source_776_; lean_object* v___y_778_; lean_object* v___x_782_; uint8_t v___x_783_; 
v_source_776_ = lean_ctor_get(v_text_775_, 0);
lean_inc_ref(v_source_776_);
v___x_782_ = lean_string_utf8_byte_size(v_source_776_);
v___x_783_ = lean_nat_dec_le(v_val_774_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v_val_774_);
v___y_778_ = v___x_782_;
goto v___jp_777_;
}
else
{
v___y_778_ = v_val_774_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v_getEnv_779_; lean_object* v___f_780_; lean_object* v___x_781_; 
v_getEnv_779_ = lean_ctor_get(v_inst_765_, 0);
lean_inc(v_getEnv_779_);
lean_dec_ref(v_inst_765_);
lean_inc(v_toBind_769_);
v___f_780_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__9), 12, 11);
lean_closure_set(v___f_780_, 0, v_inst_766_);
lean_closure_set(v___f_780_, 1, v_source_776_);
lean_closure_set(v___f_780_, 2, v_text_775_);
lean_closure_set(v___f_780_, 3, v___y_778_);
lean_closure_set(v___f_780_, 4, v_inst_767_);
lean_closure_set(v___f_780_, 5, v_toPure_768_);
lean_closure_set(v___f_780_, 6, v_toBind_769_);
lean_closure_set(v___f_780_, 7, v___x_770_);
lean_closure_set(v___f_780_, 8, v_inst_771_);
lean_closure_set(v___f_780_, 9, v_val_772_);
lean_closure_set(v___f_780_, 10, v_inst_773_);
v___x_781_ = lean_apply_4(v_toBind_769_, lean_box(0), lean_box(0), v_getEnv_779_, v___f_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_parseFailure_790_){
_start:
{
lean_object* v_toApplicative_791_; lean_object* v_toBind_792_; lean_object* v_toPure_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; 
v_toApplicative_791_ = lean_ctor_get(v_inst_784_, 0);
v_toBind_792_ = lean_ctor_get(v_inst_784_, 1);
lean_inc(v_toBind_792_);
v_toPure_793_ = lean_ctor_get(v_toApplicative_791_, 1);
lean_inc(v_toPure_793_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_Syntax_getArg(v_parseFailure_790_, v___x_794_);
v___x_796_ = 1;
v___x_797_ = l_Lean_Syntax_getPos_x3f(v___x_795_, v___x_796_);
if (lean_obj_tag(v___x_797_) == 1)
{
lean_object* v_val_798_; lean_object* v___x_799_; 
v_val_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_val_798_);
lean_dec_ref(v___x_797_);
v___x_799_ = l_Lean_Syntax_getTailPos_x3f(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
if (lean_obj_tag(v___x_799_) == 1)
{
lean_object* v_val_800_; lean_object* v___f_801_; lean_object* v___x_802_; 
v_val_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_val_800_);
lean_dec_ref(v___x_799_);
lean_inc(v_toBind_792_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__10), 11, 10);
lean_closure_set(v___f_801_, 0, v_inst_786_);
lean_closure_set(v___f_801_, 1, v_inst_788_);
lean_closure_set(v___f_801_, 2, v_inst_789_);
lean_closure_set(v___f_801_, 3, v_toPure_793_);
lean_closure_set(v___f_801_, 4, v_toBind_792_);
lean_closure_set(v___f_801_, 5, v___x_794_);
lean_closure_set(v___f_801_, 6, v_inst_784_);
lean_closure_set(v___f_801_, 7, v_val_798_);
lean_closure_set(v___f_801_, 8, v_inst_787_);
lean_closure_set(v___f_801_, 9, v_val_800_);
v___x_802_ = lean_apply_4(v_toBind_792_, lean_box(0), lean_box(0), v_inst_785_, v___f_801_);
return v___x_802_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___x_799_);
lean_dec(v_val_798_);
lean_dec(v_toBind_792_);
lean_dec_ref(v_inst_789_);
lean_dec_ref(v_inst_788_);
lean_dec(v_inst_787_);
lean_dec_ref(v_inst_786_);
lean_dec(v_inst_785_);
lean_dec_ref(v_inst_784_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_apply_2(v_toPure_793_, lean_box(0), v___x_803_);
return v___x_804_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v___x_797_);
lean_dec(v___x_795_);
lean_dec(v_toBind_792_);
lean_dec_ref(v_inst_789_);
lean_dec_ref(v_inst_788_);
lean_dec(v_inst_787_);
lean_dec_ref(v_inst_786_);
lean_dec(v_inst_785_);
lean_dec_ref(v_inst_784_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_apply_2(v_toPure_793_, lean_box(0), v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_parseFailure_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_reportVersoParseFailure___redArg(v_inst_807_, v_inst_808_, v_inst_809_, v_inst_810_, v_inst_811_, v_inst_812_, v_parseFailure_813_);
lean_dec(v_parseFailure_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_parseFailure_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_reportVersoParseFailure___redArg(v_inst_816_, v_inst_817_, v_inst_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_parseFailure_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_parseFailure_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_reportVersoParseFailure(v_m_825_, v_inst_826_, v_inst_827_, v_inst_828_, v_inst_829_, v_inst_830_, v_inst_831_, v_inst_832_, v_parseFailure_833_);
lean_dec(v_parseFailure_833_);
lean_dec_ref(v_inst_828_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_835_, size_t v_i_836_, lean_object* v_bs_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_lt(v_i_836_, v_sz_835_);
if (v___x_838_ == 0)
{
return v_bs_837_;
}
else
{
lean_object* v_v_839_; lean_object* v___x_840_; lean_object* v_bs_x27_841_; size_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
v_v_839_ = lean_array_uget(v_bs_837_, v_i_836_);
v___x_840_ = lean_unsigned_to_nat(0u);
v_bs_x27_841_ = lean_array_uset(v_bs_837_, v_i_836_, v___x_840_);
v___x_842_ = ((size_t)1ULL);
v___x_843_ = lean_usize_add(v_i_836_, v___x_842_);
v___x_844_ = lean_array_uset(v_bs_x27_841_, v_i_836_, v_v_839_);
v_i_836_ = v___x_843_;
v_bs_837_ = v___x_844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_846_, lean_object* v_i_847_, lean_object* v_bs_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_846_);
lean_dec(v_sz_846_);
v_i_boxed_850_ = lean_unbox_usize(v_i_847_);
lean_dec(v_i_847_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_849_, v_i_boxed_850_, v_bs_848_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v___x_860_, uint8_t v_suppressElabErrors_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 1)
{
lean_object* v_pre_863_; 
v_pre_863_ = lean_ctor_get(v_x_862_, 0);
switch(lean_obj_tag(v_pre_863_))
{
case 1:
{
lean_object* v_pre_864_; 
v_pre_864_ = lean_ctor_get(v_pre_863_, 0);
switch(lean_obj_tag(v_pre_864_))
{
case 0:
{
lean_object* v_str_865_; lean_object* v_str_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_str_865_ = lean_ctor_get(v_x_862_, 1);
v_str_866_ = lean_ctor_get(v_pre_863_, 1);
v___x_867_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_868_ = lean_string_dec_eq(v_str_866_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_870_ = lean_string_dec_eq(v_str_866_, v___x_869_);
if (v___x_870_ == 0)
{
return v___x_860_;
}
else
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_872_ = lean_string_dec_eq(v_str_865_, v___x_871_);
if (v___x_872_ == 0)
{
return v___x_860_;
}
else
{
return v_suppressElabErrors_861_;
}
}
}
else
{
lean_object* v___x_873_; uint8_t v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_874_ = lean_string_dec_eq(v_str_865_, v___x_873_);
if (v___x_874_ == 0)
{
return v___x_860_;
}
else
{
return v_suppressElabErrors_861_;
}
}
}
case 1:
{
lean_object* v_pre_875_; 
v_pre_875_ = lean_ctor_get(v_pre_864_, 0);
if (lean_obj_tag(v_pre_875_) == 0)
{
lean_object* v_str_876_; lean_object* v_str_877_; lean_object* v_str_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_str_876_ = lean_ctor_get(v_x_862_, 1);
v_str_877_ = lean_ctor_get(v_pre_863_, 1);
v_str_878_ = lean_ctor_get(v_pre_864_, 1);
v___x_879_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_880_ = lean_string_dec_eq(v_str_878_, v___x_879_);
if (v___x_880_ == 0)
{
return v___x_860_;
}
else
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_882_ = lean_string_dec_eq(v_str_877_, v___x_881_);
if (v___x_882_ == 0)
{
return v___x_860_;
}
else
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_884_ = lean_string_dec_eq(v_str_876_, v___x_883_);
if (v___x_884_ == 0)
{
return v___x_860_;
}
else
{
return v_suppressElabErrors_861_;
}
}
}
}
else
{
return v___x_860_;
}
}
default: 
{
return v___x_860_;
}
}
}
case 0:
{
lean_object* v_str_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_str_885_ = lean_ctor_get(v_x_862_, 1);
v___x_886_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_887_ = lean_string_dec_eq(v_str_885_, v___x_886_);
if (v___x_887_ == 0)
{
return v___x_860_;
}
else
{
return v_suppressElabErrors_861_;
}
}
default: 
{
return v___x_860_;
}
}
}
else
{
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v___x_888_, lean_object* v_suppressElabErrors_889_, lean_object* v_x_890_){
_start:
{
uint8_t v___x_10517__boxed_891_; uint8_t v_suppressElabErrors_boxed_892_; uint8_t v_res_893_; lean_object* v_r_894_; 
v___x_10517__boxed_891_ = lean_unbox(v___x_888_);
v_suppressElabErrors_boxed_892_ = lean_unbox(v_suppressElabErrors_889_);
v_res_893_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_10517__boxed_891_, v_suppressElabErrors_boxed_892_, v_x_890_);
lean_dec(v_x_890_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v___x_895_, uint8_t v_suppressElabErrors_896_, lean_object* v_x_897_){
_start:
{
if (lean_obj_tag(v_x_897_) == 1)
{
lean_object* v_pre_898_; 
v_pre_898_ = lean_ctor_get(v_x_897_, 0);
switch(lean_obj_tag(v_pre_898_))
{
case 1:
{
lean_object* v_pre_899_; 
v_pre_899_ = lean_ctor_get(v_pre_898_, 0);
switch(lean_obj_tag(v_pre_899_))
{
case 0:
{
lean_object* v_str_900_; lean_object* v_str_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_str_900_ = lean_ctor_get(v_x_897_, 1);
v_str_901_ = lean_ctor_get(v_pre_898_, 1);
v___x_902_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_903_ = lean_string_dec_eq(v_str_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_905_ = lean_string_dec_eq(v_str_901_, v___x_904_);
if (v___x_905_ == 0)
{
return v___x_895_;
}
else
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_907_ = lean_string_dec_eq(v_str_900_, v___x_906_);
if (v___x_907_ == 0)
{
return v___x_895_;
}
else
{
return v_suppressElabErrors_896_;
}
}
}
else
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_909_ = lean_string_dec_eq(v_str_900_, v___x_908_);
if (v___x_909_ == 0)
{
return v___x_895_;
}
else
{
return v_suppressElabErrors_896_;
}
}
}
case 1:
{
lean_object* v_pre_910_; 
v_pre_910_ = lean_ctor_get(v_pre_899_, 0);
if (lean_obj_tag(v_pre_910_) == 0)
{
lean_object* v_str_911_; lean_object* v_str_912_; lean_object* v_str_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_str_911_ = lean_ctor_get(v_x_897_, 1);
v_str_912_ = lean_ctor_get(v_pre_898_, 1);
v_str_913_ = lean_ctor_get(v_pre_899_, 1);
v___x_914_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_915_ = lean_string_dec_eq(v_str_913_, v___x_914_);
if (v___x_915_ == 0)
{
return v___x_895_;
}
else
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_917_ = lean_string_dec_eq(v_str_912_, v___x_916_);
if (v___x_917_ == 0)
{
return v___x_895_;
}
else
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_919_ = lean_string_dec_eq(v_str_911_, v___x_918_);
if (v___x_919_ == 0)
{
return v___x_895_;
}
else
{
return v_suppressElabErrors_896_;
}
}
}
}
else
{
return v___x_895_;
}
}
default: 
{
return v___x_895_;
}
}
}
case 0:
{
lean_object* v_str_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_str_920_ = lean_ctor_get(v_x_897_, 1);
v___x_921_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_922_ = lean_string_dec_eq(v_str_920_, v___x_921_);
if (v___x_922_ == 0)
{
return v___x_895_;
}
else
{
return v_suppressElabErrors_896_;
}
}
default: 
{
return v___x_895_;
}
}
}
else
{
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___x_923_, lean_object* v_suppressElabErrors_924_, lean_object* v_x_925_){
_start:
{
uint8_t v___x_10589__boxed_926_; uint8_t v_suppressElabErrors_boxed_927_; uint8_t v_res_928_; lean_object* v_r_929_; 
v___x_10589__boxed_926_ = lean_unbox(v___x_923_);
v_suppressElabErrors_boxed_927_ = lean_unbox(v_suppressElabErrors_924_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10589__boxed_926_, v_suppressElabErrors_boxed_927_, v_x_925_);
lean_dec(v_x_925_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_930_, lean_object* v___x_931_, lean_object* v_as_932_, size_t v_sz_933_, size_t v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_a_940_; uint8_t v___x_944_; 
v___x_944_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_930_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v_b_935_);
return v___x_945_;
}
else
{
lean_object* v_a_946_; lean_object* v_snd_947_; lean_object* v_fst_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1005_; 
v_a_946_ = lean_array_uget(v_as_932_, v_i_934_);
v_snd_947_ = lean_ctor_get(v_a_946_, 1);
v_fst_948_ = lean_ctor_get(v_a_946_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_950_ = v_a_946_;
v_isShared_951_ = v_isSharedCheck_1005_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_947_);
lean_inc(v_fst_948_);
lean_dec(v_a_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1005_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1003_; 
v_snd_952_ = lean_ctor_get(v_snd_947_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_snd_947_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_snd_947_, 0);
lean_dec(v_unused_1004_);
v___x_954_ = v_snd_947_;
v_isShared_955_ = v_isSharedCheck_1003_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_dec(v_snd_947_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1003_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v_fileName_956_; uint8_t v_suppressElabErrors_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___y_969_; lean_object* v___y_970_; 
v_fileName_956_ = lean_ctor_get(v___y_936_, 0);
v_suppressElabErrors_957_ = lean_ctor_get_uint8(v___y_936_, sizeof(void*)*14 + 1);
v___x_958_ = lean_box(0);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_nat_dec_eq(v___x_931_, v___x_959_);
lean_inc_ref(v___x_930_);
v___x_961_ = l_Lean_FileMap_toPosition(v___x_930_, v_fst_948_);
lean_dec(v_fst_948_);
v___x_962_ = lean_box(0);
v___x_963_ = 2;
v___x_964_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_965_ = l_Lean_Parser_Error_toString(v_snd_952_);
v___x_966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
v___x_967_ = l_Lean_MessageData_ofFormat(v___x_966_);
if (v_suppressElabErrors_957_ == 0)
{
v___y_969_ = v___y_936_;
v___y_970_ = v___y_937_;
goto v___jp_968_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; uint8_t v___x_1002_; 
v___x_999_ = lean_box(v___x_960_);
v___x_1000_ = lean_box(v_suppressElabErrors_957_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1001_, 0, v___x_999_);
lean_closure_set(v___f_1001_, 1, v___x_1000_);
lean_inc_ref(v___x_967_);
v___x_1002_ = l_Lean_MessageData_hasTag(v___f_1001_, v___x_967_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v___x_967_);
lean_dec_ref(v___x_961_);
lean_del_object(v___x_954_);
lean_del_object(v___x_950_);
v_a_940_ = v___x_958_;
goto v___jp_939_;
}
else
{
v___y_969_ = v___y_936_;
v___y_970_ = v___y_937_;
goto v___jp_968_;
}
}
v___jp_968_:
{
lean_object* v___x_971_; lean_object* v_currNamespace_972_; lean_object* v_openDecls_973_; lean_object* v___x_975_; 
v___x_971_ = lean_st_ref_take(v___y_970_);
v_currNamespace_972_ = lean_ctor_get(v___y_969_, 6);
v_openDecls_973_ = lean_ctor_get(v___y_969_, 7);
lean_inc(v_openDecls_973_);
lean_inc(v_currNamespace_972_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_openDecls_973_);
lean_ctor_set(v___x_954_, 0, v_currNamespace_972_);
v___x_975_ = v___x_954_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_currNamespace_972_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_openDecls_973_);
v___x_975_ = v_reuseFailAlloc_998_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set_tag(v___x_950_, 4);
lean_ctor_set(v___x_950_, 1, v___x_967_);
lean_ctor_set(v___x_950_, 0, v___x_975_);
v___x_977_ = v___x_950_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_967_);
v___x_977_ = v_reuseFailAlloc_997_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v_nextMacroScope_980_; lean_object* v_ngen_981_; lean_object* v_auxDeclNGen_982_; lean_object* v_traceState_983_; lean_object* v_cache_984_; lean_object* v_messages_985_; lean_object* v_infoState_986_; lean_object* v_snapshotTasks_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
lean_inc_ref(v_fileName_956_);
v___x_978_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_978_, 0, v_fileName_956_);
lean_ctor_set(v___x_978_, 1, v___x_961_);
lean_ctor_set(v___x_978_, 2, v___x_962_);
lean_ctor_set(v___x_978_, 3, v___x_964_);
lean_ctor_set(v___x_978_, 4, v___x_977_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*5, v___x_960_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*5 + 1, v___x_963_);
lean_ctor_set_uint8(v___x_978_, sizeof(void*)*5 + 2, v___x_960_);
v_env_979_ = lean_ctor_get(v___x_971_, 0);
v_nextMacroScope_980_ = lean_ctor_get(v___x_971_, 1);
v_ngen_981_ = lean_ctor_get(v___x_971_, 2);
v_auxDeclNGen_982_ = lean_ctor_get(v___x_971_, 3);
v_traceState_983_ = lean_ctor_get(v___x_971_, 4);
v_cache_984_ = lean_ctor_get(v___x_971_, 5);
v_messages_985_ = lean_ctor_get(v___x_971_, 6);
v_infoState_986_ = lean_ctor_get(v___x_971_, 7);
v_snapshotTasks_987_ = lean_ctor_get(v___x_971_, 8);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_996_ == 0)
{
v___x_989_ = v___x_971_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_snapshotTasks_987_);
lean_inc(v_infoState_986_);
lean_inc(v_messages_985_);
lean_inc(v_cache_984_);
lean_inc(v_traceState_983_);
lean_inc(v_auxDeclNGen_982_);
lean_inc(v_ngen_981_);
lean_inc(v_nextMacroScope_980_);
lean_inc(v_env_979_);
lean_dec(v___x_971_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_MessageLog_add(v___x_978_, v_messages_985_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 6, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_env_979_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_nextMacroScope_980_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_ngen_981_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_auxDeclNGen_982_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_traceState_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 5, v_cache_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 6, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 7, v_infoState_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 8, v_snapshotTasks_987_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_st_ref_set(v___y_970_, v___x_993_);
v_a_940_ = v___x_958_;
goto v___jp_939_;
}
}
}
}
}
}
}
}
v___jp_939_:
{
size_t v___x_941_; size_t v___x_942_; 
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_934_, v___x_941_);
v_i_934_ = v___x_942_;
v_b_935_ = v_a_940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_as_1008_, lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_b_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
size_t v_sz_boxed_1015_; size_t v_i_boxed_1016_; lean_object* v_res_1017_; 
v_sz_boxed_1015_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1006_, v___x_1007_, v_as_1008_, v_sz_boxed_1015_, v_i_boxed_1016_, v_b_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_as_1008_);
lean_dec(v___x_1007_);
return v_res_1017_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_box(1);
v___x_1019_ = l_Lean_MessageData_ofFormat(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__2));
v___x_1024_ = l_Lean_MessageData_ofFormat(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
if (lean_obj_tag(v_x_1026_) == 0)
{
return v_x_1025_;
}
else
{
lean_object* v_head_1027_; lean_object* v_tail_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1050_; 
v_head_1027_ = lean_ctor_get(v_x_1026_, 0);
v_tail_1028_ = lean_ctor_get(v_x_1026_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1026_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1030_ = v_x_1026_;
v_isShared_1031_ = v_isSharedCheck_1050_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_tail_1028_);
lean_inc(v_head_1027_);
lean_dec(v_x_1026_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1050_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_before_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1048_; 
v_before_1032_ = lean_ctor_get(v_head_1027_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_head_1027_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_head_1027_, 1);
lean_dec(v_unused_1049_);
v___x_1034_ = v_head_1027_;
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_before_1032_);
lean_dec(v_head_1027_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 7);
lean_ctor_set(v___x_1034_, 1, v___x_1036_);
lean_ctor_set(v___x_1034_, 0, v_x_1025_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_x_1025_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__3);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 7);
lean_ctor_set(v___x_1030_, 1, v___x_1039_);
lean_ctor_set(v___x_1030_, 0, v___x_1038_);
v___x_1041_ = v___x_1030_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = l_Lean_MessageData_ofSyntax(v_before_1032_);
v___x_1043_ = l_Lean_indentD(v___x_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1041_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v_x_1025_ = v___x_1044_;
v_x_1026_ = v_tail_1028_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(lean_object* v_opts_1051_, lean_object* v_opt_1052_){
_start:
{
lean_object* v_name_1053_; lean_object* v_defValue_1054_; lean_object* v_map_1055_; lean_object* v___x_1056_; 
v_name_1053_ = lean_ctor_get(v_opt_1052_, 0);
v_defValue_1054_ = lean_ctor_get(v_opt_1052_, 1);
v_map_1055_ = lean_ctor_get(v_opts_1051_, 0);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1055_, v_name_1053_);
if (lean_obj_tag(v___x_1056_) == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_unbox(v_defValue_1054_);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_val_1058_);
lean_dec_ref(v___x_1056_);
if (lean_obj_tag(v_val_1058_) == 1)
{
uint8_t v_v_1059_; 
v_v_1059_ = lean_ctor_get_uint8(v_val_1058_, 0);
lean_dec_ref(v_val_1058_);
return v_v_1059_;
}
else
{
uint8_t v___x_1060_; 
lean_dec(v_val_1058_);
v___x_1060_ = lean_unbox(v_defValue_1054_);
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_opts_1061_, lean_object* v_opt_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_opts_1061_, v_opt_1062_);
lean_dec_ref(v_opt_1062_);
lean_dec_ref(v_opts_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__1));
v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(lean_object* v_msgData_1070_, lean_object* v_macroStack_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_options_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_options_1074_ = lean_ctor_get(v___y_1072_, 2);
v___x_1075_ = l_Lean_Elab_pp_macroStack;
v___x_1076_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
lean_dec(v_macroStack_1071_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_msgData_1070_);
return v___x_1077_;
}
else
{
if (lean_obj_tag(v_macroStack_1071_) == 0)
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_msgData_1070_);
return v___x_1078_;
}
else
{
lean_object* v_head_1079_; lean_object* v_after_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1095_; 
v_head_1079_ = lean_ctor_get(v_macroStack_1071_, 0);
lean_inc(v_head_1079_);
v_after_1080_ = lean_ctor_get(v_head_1079_, 1);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_head_1079_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v_head_1079_, 0);
lean_dec(v_unused_1096_);
v___x_1082_ = v_head_1079_;
v_isShared_1083_ = v_isSharedCheck_1095_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_after_1080_);
lean_dec(v_head_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1095_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7___closed__0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set_tag(v___x_1082_, 7);
lean_ctor_set(v___x_1082_, 1, v___x_1084_);
lean_ctor_set(v___x_1082_, 0, v_msgData_1070_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_msgData_1070_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_msgData_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1087_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___closed__2);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_MessageData_ofSyntax(v_after_1080_);
v___x_1090_ = l_Lean_indentD(v___x_1089_);
v_msgData_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1091_, 0, v___x_1088_);
lean_ctor_set(v_msgData_1091_, 1, v___x_1090_);
v___x_1092_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__7(v_msgData_1091_, v_macroStack_1071_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_msgData_1097_, lean_object* v_macroStack_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1097_, v_macroStack_1098_, v___y_1099_);
lean_dec_ref(v___y_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_env_1109_; lean_object* v___x_1110_; lean_object* v_mctx_1111_; lean_object* v_lctx_1112_; lean_object* v_options_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1108_ = lean_st_ref_get(v___y_1106_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1110_ = lean_st_ref_get(v___y_1104_);
v_mctx_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_mctx_1111_);
lean_dec(v___x_1110_);
v_lctx_1112_ = lean_ctor_get(v___y_1103_, 2);
v_options_1113_ = lean_ctor_get(v___y_1105_, 2);
lean_inc_ref(v_options_1113_);
lean_inc_ref(v_lctx_1112_);
v___x_1114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1114_, 0, v_env_1109_);
lean_ctor_set(v___x_1114_, 1, v_mctx_1111_);
lean_ctor_set(v___x_1114_, 2, v_lctx_1112_);
lean_ctor_set(v___x_1114_, 3, v_options_1113_);
v___x_1115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v_msgData_1102_);
v___x_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v_macroStack_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1146_; 
v_ref_1132_ = lean_ctor_get(v___y_1129_, 5);
v___x_1133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msg_1124_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref(v___x_1133_);
v_macroStack_1135_ = lean_ctor_get(v___y_1125_, 1);
lean_inc(v_macroStack_1135_);
lean_dec_ref(v___y_1125_);
lean_inc(v_macroStack_1135_);
v___x_1136_ = l_Lean_Elab_getBetterRef(v_ref_1132_, v_macroStack_1135_);
v___x_1137_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_a_1134_, v_macroStack_1135_, v___y_1129_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1136_);
lean_ctor_set(v___x_1142_, 1, v_a_1138_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set_tag(v___x_1140_, 1);
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1156_, lean_object* v_msg_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_fileName_1165_; lean_object* v_fileMap_1166_; lean_object* v_options_1167_; lean_object* v_currRecDepth_1168_; lean_object* v_maxRecDepth_1169_; lean_object* v_ref_1170_; lean_object* v_currNamespace_1171_; lean_object* v_openDecls_1172_; lean_object* v_initHeartbeats_1173_; lean_object* v_maxHeartbeats_1174_; lean_object* v_quotContext_1175_; lean_object* v_currMacroScope_1176_; uint8_t v_diag_1177_; lean_object* v_cancelTk_x3f_1178_; uint8_t v_suppressElabErrors_1179_; lean_object* v_inheritedTraceOptions_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_fileName_1165_ = lean_ctor_get(v___y_1162_, 0);
v_fileMap_1166_ = lean_ctor_get(v___y_1162_, 1);
v_options_1167_ = lean_ctor_get(v___y_1162_, 2);
v_currRecDepth_1168_ = lean_ctor_get(v___y_1162_, 3);
v_maxRecDepth_1169_ = lean_ctor_get(v___y_1162_, 4);
v_ref_1170_ = lean_ctor_get(v___y_1162_, 5);
v_currNamespace_1171_ = lean_ctor_get(v___y_1162_, 6);
v_openDecls_1172_ = lean_ctor_get(v___y_1162_, 7);
v_initHeartbeats_1173_ = lean_ctor_get(v___y_1162_, 8);
v_maxHeartbeats_1174_ = lean_ctor_get(v___y_1162_, 9);
v_quotContext_1175_ = lean_ctor_get(v___y_1162_, 10);
v_currMacroScope_1176_ = lean_ctor_get(v___y_1162_, 11);
v_diag_1177_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*14);
v_cancelTk_x3f_1178_ = lean_ctor_get(v___y_1162_, 12);
v_suppressElabErrors_1179_ = lean_ctor_get_uint8(v___y_1162_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1180_ = lean_ctor_get(v___y_1162_, 13);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___y_1162_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v___y_1162_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_inheritedTraceOptions_1180_);
lean_inc(v_cancelTk_x3f_1178_);
lean_inc(v_currMacroScope_1176_);
lean_inc(v_quotContext_1175_);
lean_inc(v_maxHeartbeats_1174_);
lean_inc(v_initHeartbeats_1173_);
lean_inc(v_openDecls_1172_);
lean_inc(v_currNamespace_1171_);
lean_inc(v_ref_1170_);
lean_inc(v_maxRecDepth_1169_);
lean_inc(v_currRecDepth_1168_);
lean_inc(v_options_1167_);
lean_inc(v_fileMap_1166_);
lean_inc(v_fileName_1165_);
lean_dec(v___y_1162_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_ref_1184_; lean_object* v___x_1186_; 
v_ref_1184_ = l_Lean_replaceRef(v_ref_1156_, v_ref_1170_);
lean_dec(v_ref_1170_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 5, v_ref_1184_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_fileName_1165_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_fileMap_1166_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_options_1167_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_currRecDepth_1168_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_maxRecDepth_1169_);
lean_ctor_set(v_reuseFailAlloc_1188_, 5, v_ref_1184_);
lean_ctor_set(v_reuseFailAlloc_1188_, 6, v_currNamespace_1171_);
lean_ctor_set(v_reuseFailAlloc_1188_, 7, v_openDecls_1172_);
lean_ctor_set(v_reuseFailAlloc_1188_, 8, v_initHeartbeats_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 9, v_maxHeartbeats_1174_);
lean_ctor_set(v_reuseFailAlloc_1188_, 10, v_quotContext_1175_);
lean_ctor_set(v_reuseFailAlloc_1188_, 11, v_currMacroScope_1176_);
lean_ctor_set(v_reuseFailAlloc_1188_, 12, v_cancelTk_x3f_1178_);
lean_ctor_set(v_reuseFailAlloc_1188_, 13, v_inheritedTraceOptions_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, sizeof(void*)*14, v_diag_1177_);
lean_ctor_set_uint8(v_reuseFailAlloc_1188_, sizeof(void*)*14 + 1, v_suppressElabErrors_1179_);
v___x_1186_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___x_1186_, v___y_1163_);
lean_dec_ref(v___x_1186_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1190_, v_msg_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v_ref_1190_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; uint8_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; uint8_t v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; uint8_t v___y_1312_; uint8_t v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
lean_inc(v_docComment_1200_);
v___x_1373_ = l_Lean_Syntax_getKind(v_docComment_1200_);
v___x_1374_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_1375_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_1376_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_1377_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_1378_ = lean_name_eq(v___x_1373_, v___x_1377_);
lean_dec(v___x_1373_);
if (v___x_1378_ == 0)
{
goto v___jp_1350_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = l_Lean_Syntax_getArg(v_docComment_1200_, v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v_kind_1381_; 
v_kind_1381_ = lean_ctor_get(v___x_1380_, 1);
lean_inc(v_kind_1381_);
if (lean_obj_tag(v_kind_1381_) == 1)
{
lean_object* v_pre_1382_; 
v_pre_1382_ = lean_ctor_get(v_kind_1381_, 0);
lean_inc(v_pre_1382_);
if (lean_obj_tag(v_pre_1382_) == 1)
{
lean_object* v_pre_1383_; 
v_pre_1383_ = lean_ctor_get(v_pre_1382_, 0);
lean_inc(v_pre_1383_);
if (lean_obj_tag(v_pre_1383_) == 1)
{
lean_object* v_pre_1384_; 
v_pre_1384_ = lean_ctor_get(v_pre_1383_, 0);
lean_inc(v_pre_1384_);
if (lean_obj_tag(v_pre_1384_) == 1)
{
lean_object* v_pre_1385_; 
v_pre_1385_ = lean_ctor_get(v_pre_1384_, 0);
lean_inc(v_pre_1385_);
if (lean_obj_tag(v_pre_1385_) == 0)
{
lean_object* v_info_1386_; lean_object* v_args_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1413_; 
v_info_1386_ = lean_ctor_get(v___x_1380_, 0);
v_args_1387_ = lean_ctor_get(v___x_1380_, 2);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1380_, 1);
lean_dec(v_unused_1414_);
v___x_1389_ = v___x_1380_;
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_args_1387_);
lean_inc(v_info_1386_);
lean_dec(v___x_1380_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_str_1391_; lean_object* v_str_1392_; lean_object* v_str_1393_; lean_object* v_str_1394_; uint8_t v___x_1395_; 
v_str_1391_ = lean_ctor_get(v_kind_1381_, 1);
lean_inc_ref(v_str_1391_);
lean_dec_ref(v_kind_1381_);
v_str_1392_ = lean_ctor_get(v_pre_1382_, 1);
lean_inc_ref(v_str_1392_);
lean_dec_ref(v_pre_1382_);
v_str_1393_ = lean_ctor_get(v_pre_1383_, 1);
lean_inc_ref(v_str_1393_);
lean_dec_ref(v_pre_1383_);
v_str_1394_ = lean_ctor_get(v_pre_1384_, 1);
lean_inc_ref(v_str_1394_);
lean_dec_ref(v_pre_1384_);
v___x_1395_ = lean_string_dec_eq(v_str_1394_, v___x_1374_);
lean_dec_ref(v_str_1394_);
if (v___x_1395_ == 0)
{
lean_dec_ref(v_str_1393_);
lean_dec_ref(v_str_1392_);
lean_dec_ref(v_str_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref(v_args_1387_);
lean_dec(v_info_1386_);
goto v___jp_1350_;
}
else
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_string_dec_eq(v_str_1393_, v___x_1375_);
lean_dec_ref(v_str_1393_);
if (v___x_1396_ == 0)
{
lean_dec_ref(v_str_1392_);
lean_dec_ref(v_str_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref(v_args_1387_);
lean_dec(v_info_1386_);
goto v___jp_1350_;
}
else
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_string_dec_eq(v_str_1392_, v___x_1376_);
lean_dec_ref(v_str_1392_);
if (v___x_1397_ == 0)
{
lean_dec_ref(v_str_1391_);
lean_del_object(v___x_1389_);
lean_dec_ref(v_args_1387_);
lean_dec(v_info_1386_);
goto v___jp_1350_;
}
else
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_1399_ = lean_string_dec_eq(v_str_1391_, v___x_1398_);
lean_dec_ref(v_str_1391_);
if (v___x_1399_ == 0)
{
lean_del_object(v___x_1389_);
lean_dec_ref(v_args_1387_);
lean_dec(v_info_1386_);
goto v___jp_1350_;
}
else
{
lean_dec_ref(v___y_1205_);
lean_dec_ref(v___y_1201_);
lean_dec(v_docComment_1200_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_del_object(v___x_1389_);
lean_dec_ref(v_args_1387_);
lean_dec(v_info_1386_);
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1402_ = l_Lean_Name_str___override(v_pre_1385_, v___x_1374_);
v___x_1403_ = l_Lean_Name_str___override(v___x_1402_, v___x_1375_);
v___x_1404_ = l_Lean_Name_str___override(v___x_1403_, v___x_1376_);
v___x_1405_ = l_Lean_Name_str___override(v___x_1404_, v___x_1398_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___x_1405_);
v___x_1407_ = v___x_1389_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_info_1386_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_args_1387_);
v___x_1407_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = l_Lean_Syntax_getArg(v___x_1407_, v___x_1408_);
lean_dec_ref(v___x_1407_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
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
lean_dec_ref(v_pre_1384_);
lean_dec(v_pre_1385_);
lean_dec_ref(v_pre_1383_);
lean_dec_ref(v_pre_1382_);
lean_dec_ref(v_kind_1381_);
lean_dec_ref(v___x_1380_);
goto v___jp_1350_;
}
}
else
{
lean_dec_ref(v_pre_1383_);
lean_dec(v_pre_1384_);
lean_dec_ref(v_pre_1382_);
lean_dec_ref(v_kind_1381_);
lean_dec_ref(v___x_1380_);
goto v___jp_1350_;
}
}
else
{
lean_dec(v_pre_1383_);
lean_dec_ref(v_pre_1382_);
lean_dec_ref(v_kind_1381_);
lean_dec_ref(v___x_1380_);
goto v___jp_1350_;
}
}
else
{
lean_dec_ref(v_kind_1381_);
lean_dec(v_pre_1382_);
lean_dec_ref(v___x_1380_);
goto v___jp_1350_;
}
}
else
{
lean_dec_ref(v___x_1380_);
lean_dec(v_kind_1381_);
goto v___jp_1350_;
}
}
else
{
lean_dec(v___x_1380_);
goto v___jp_1350_;
}
}
v___jp_1208_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
v___jp_1211_:
{
lean_object* v___x_1221_; lean_object* v_currNamespace_1222_; lean_object* v_openDecls_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_traceState_1231_; lean_object* v_cache_1232_; lean_object* v_messages_1233_; lean_object* v_infoState_1234_; lean_object* v_snapshotTasks_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1244_; 
v___x_1221_ = lean_st_ref_take(v___y_1220_);
v_currNamespace_1222_ = lean_ctor_get(v___y_1219_, 6);
lean_inc(v_currNamespace_1222_);
v_openDecls_1223_ = lean_ctor_get(v___y_1219_, 7);
lean_inc(v_openDecls_1223_);
lean_dec_ref(v___y_1219_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_currNamespace_1222_);
lean_ctor_set(v___x_1224_, 1, v_openDecls_1223_);
v___x_1225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___y_1214_);
v___x_1226_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1226_, 0, v___y_1218_);
lean_ctor_set(v___x_1226_, 1, v___y_1216_);
lean_ctor_set(v___x_1226_, 2, v___y_1212_);
lean_ctor_set(v___x_1226_, 3, v___y_1215_);
lean_ctor_set(v___x_1226_, 4, v___x_1225_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*5, v___y_1213_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*5 + 1, v___y_1217_);
lean_ctor_set_uint8(v___x_1226_, sizeof(void*)*5 + 2, v___y_1213_);
v_env_1227_ = lean_ctor_get(v___x_1221_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1221_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1231_ = lean_ctor_get(v___x_1221_, 4);
v_cache_1232_ = lean_ctor_get(v___x_1221_, 5);
v_messages_1233_ = lean_ctor_get(v___x_1221_, 6);
v_infoState_1234_ = lean_ctor_get(v___x_1221_, 7);
v_snapshotTasks_1235_ = lean_ctor_get(v___x_1221_, 8);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1237_ = v___x_1221_;
v_isShared_1238_ = v_isSharedCheck_1244_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snapshotTasks_1235_);
lean_inc(v_infoState_1234_);
lean_inc(v_messages_1233_);
lean_inc(v_cache_1232_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1221_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1244_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_MessageLog_add(v___x_1226_, v_messages_1233_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 6, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_env_1227_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_traceState_1231_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v_cache_1232_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_infoState_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 8, v_snapshotTasks_1235_);
v___x_1241_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_st_ref_set(v___y_1220_, v___x_1241_);
goto v___jp_1208_;
}
}
}
v___jp_1245_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
lean_inc_ref(v___y_1252_);
v___x_1253_ = l_Lean_Parser_ParserState_allErrors(v___y_1252_);
v___x_1254_ = lean_array_get_size(v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_nat_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; size_t v_sz_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1248_);
v___x_1257_ = lean_box(0);
v_sz_1258_ = lean_array_size(v___x_1253_);
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1247_, v___x_1254_, v___x_1253_, v_sz_1258_, v___x_1259_, v___x_1257_, v___y_1205_, v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec_ref(v___x_1253_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1268_; 
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1269_);
v___x_1262_ = v___x_1260_;
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v___x_1260_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1268_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_box(0);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1264_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1260_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_stxStack_1278_; lean_object* v_pos_1279_; uint8_t v___x_1280_; 
lean_dec_ref(v___x_1253_);
v_stxStack_1278_ = lean_ctor_get(v___y_1252_, 0);
lean_inc_ref(v_stxStack_1278_);
v_pos_1279_ = lean_ctor_get(v___y_1252_, 2);
lean_inc(v_pos_1279_);
lean_dec_ref(v___y_1252_);
v___x_1280_ = l_Lean_Parser_InputContext_atEnd(v___y_1248_, v_pos_1279_);
lean_dec_ref(v___y_1248_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint32_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_stxStack_1278_);
v___x_1281_ = l_Lean_FileMap_toPosition(v___y_1247_, v_pos_1279_);
v___x_1282_ = lean_box(0);
v___x_1283_ = 2;
v___x_1284_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1285_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1286_ = lean_string_utf8_get(v___y_1250_, v_pos_1279_);
lean_dec(v_pos_1279_);
lean_dec_ref(v___y_1250_);
v___x_1287_ = lean_string_push(v___x_1284_, v___x_1286_);
v___x_1288_ = lean_string_append(v___x_1285_, v___x_1287_);
lean_dec_ref(v___x_1287_);
v___x_1289_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1290_ = lean_string_append(v___x_1288_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
v___x_1292_ = l_Lean_MessageData_ofFormat(v___x_1291_);
if (v___y_1249_ == 0)
{
v___y_1212_ = v___x_1282_;
v___y_1213_ = v___x_1280_;
v___y_1214_ = v___x_1292_;
v___y_1215_ = v___x_1284_;
v___y_1216_ = v___x_1281_;
v___y_1217_ = v___x_1283_;
v___y_1218_ = v___y_1251_;
v___y_1219_ = v___y_1205_;
v___y_1220_ = v___y_1206_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___f_1295_; uint8_t v___x_1296_; 
v___x_1293_ = lean_box(v___x_1280_);
v___x_1294_ = lean_box(v___y_1246_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1295_, 0, v___x_1293_);
lean_closure_set(v___f_1295_, 1, v___x_1294_);
lean_inc_ref(v___x_1292_);
v___x_1296_ = l_Lean_MessageData_hasTag(v___f_1295_, v___x_1292_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v___x_1281_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1205_);
goto v___jp_1208_;
}
else
{
v___y_1212_ = v___x_1282_;
v___y_1213_ = v___x_1280_;
v___y_1214_ = v___x_1292_;
v___y_1215_ = v___x_1284_;
v___y_1216_ = v___x_1281_;
v___y_1217_ = v___x_1283_;
v___y_1218_ = v___y_1251_;
v___y_1219_ = v___y_1205_;
v___y_1220_ = v___y_1206_;
goto v___jp_1211_;
}
}
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec(v_pos_1279_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec_ref(v___y_1247_);
lean_dec_ref(v___y_1205_);
v___x_1297_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1278_);
lean_dec_ref(v_stxStack_1278_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
}
v___jp_1300_:
{
if (v___y_1312_ == 0)
{
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1308_);
lean_dec_ref(v___y_1306_);
lean_dec_ref(v___y_1305_);
v___y_1246_ = v___y_1301_;
v___y_1247_ = v___y_1302_;
v___y_1248_ = v___y_1303_;
v___y_1249_ = v___y_1304_;
v___y_1250_ = v___y_1309_;
v___y_1251_ = v___y_1310_;
v___y_1252_ = v___y_1307_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_pos_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1311_);
lean_ctor_set(v___x_1316_, 1, v___x_1313_);
v___x_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1313_);
lean_ctor_set(v___x_1317_, 1, v___x_1314_);
lean_ctor_set(v___x_1317_, 2, v___x_1315_);
lean_ctor_set(v___x_1317_, 3, v___x_1316_);
lean_ctor_set(v___x_1317_, 4, v___x_1313_);
v_pos_1318_ = lean_ctor_get(v___y_1307_, 2);
lean_inc(v_pos_1318_);
lean_dec_ref(v___y_1307_);
v___x_1319_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_1319_, 0, v___x_1317_);
v___x_1320_ = l_Lean_Parser_ParserState_setPos(v___y_1305_, v_pos_1318_);
lean_inc_ref(v___y_1303_);
v___x_1321_ = l_Lean_Parser_ParserFn_run(v___x_1319_, v___y_1303_, v___y_1306_, v___y_1308_, v___x_1320_);
v___y_1246_ = v___y_1301_;
v___y_1247_ = v___y_1302_;
v___y_1248_ = v___y_1303_;
v___y_1249_ = v___y_1304_;
v___y_1250_ = v___y_1309_;
v___y_1251_ = v___y_1310_;
v___y_1252_ = v___x_1321_;
goto v___jp_1245_;
}
}
v___jp_1322_:
{
lean_object* v___x_1334_; lean_object* v_env_1335_; lean_object* v_ictx_1336_; lean_object* v_pmctx_1337_; lean_object* v_blockCtxt_1338_; lean_object* v___x_1339_; lean_object* v_s_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_s_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1334_ = lean_st_ref_get(v___y_1206_);
v_env_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc_ref(v_env_1335_);
lean_dec(v___x_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1326_);
lean_inc_ref(v___y_1330_);
lean_inc_ref(v___y_1324_);
v_ictx_1336_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1336_, 0, v___y_1324_);
lean_ctor_set(v_ictx_1336_, 1, v___y_1330_);
lean_ctor_set(v_ictx_1336_, 2, v___y_1326_);
lean_ctor_set(v_ictx_1336_, 3, v___y_1333_);
lean_inc_ref(v_env_1335_);
v_pmctx_1337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1337_, 0, v_env_1335_);
lean_ctor_set(v_pmctx_1337_, 1, v___y_1325_);
lean_ctor_set(v_pmctx_1337_, 2, v___y_1329_);
lean_ctor_set(v_pmctx_1337_, 3, v___y_1328_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1326_);
v_blockCtxt_1338_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1326_, v___y_1332_, v___y_1333_);
v___x_1339_ = l_Lean_Parser_mkParserState(v___y_1324_);
lean_inc_ref(v___x_1339_);
v_s_1340_ = l_Lean_Parser_ParserState_setPos(v___x_1339_, v___y_1332_);
v___x_1341_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_1341_, 0, v_blockCtxt_1338_);
v___x_1342_ = l_Lean_Parser_getTokenTable(v_env_1335_);
lean_inc_ref(v___x_1342_);
lean_inc_ref(v_pmctx_1337_);
lean_inc_ref(v_ictx_1336_);
v_s_1343_ = l_Lean_Parser_ParserFn_run(v___x_1341_, v_ictx_1336_, v_pmctx_1337_, v___x_1342_, v_s_1340_);
lean_inc_ref(v_s_1343_);
v___x_1344_ = l_Lean_Parser_ParserState_allErrors(v_s_1343_);
v___x_1345_ = lean_array_get_size(v___x_1344_);
lean_dec_ref(v___x_1344_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_nat_dec_eq(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
v___y_1301_ = v___y_1323_;
v___y_1302_ = v___y_1326_;
v___y_1303_ = v_ictx_1336_;
v___y_1304_ = v___y_1327_;
v___y_1305_ = v___x_1339_;
v___y_1306_ = v_pmctx_1337_;
v___y_1307_ = v_s_1343_;
v___y_1308_ = v___x_1342_;
v___y_1309_ = v___y_1324_;
v___y_1310_ = v___y_1330_;
v___y_1311_ = v___y_1331_;
v___y_1312_ = v___x_1347_;
goto v___jp_1300_;
}
else
{
lean_object* v_pos_1348_; uint8_t v___x_1349_; 
v_pos_1348_ = lean_ctor_get(v_s_1343_, 2);
lean_inc(v_pos_1348_);
v___x_1349_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1336_, v_pos_1348_);
lean_dec(v_pos_1348_);
if (v___x_1349_ == 0)
{
v___y_1301_ = v___y_1323_;
v___y_1302_ = v___y_1326_;
v___y_1303_ = v_ictx_1336_;
v___y_1304_ = v___y_1327_;
v___y_1305_ = v___x_1339_;
v___y_1306_ = v_pmctx_1337_;
v___y_1307_ = v_s_1343_;
v___y_1308_ = v___x_1342_;
v___y_1309_ = v___y_1324_;
v___y_1310_ = v___y_1330_;
v___y_1311_ = v___y_1331_;
v___y_1312_ = v___x_1347_;
goto v___jp_1300_;
}
else
{
lean_dec_ref(v___x_1342_);
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_pmctx_1337_);
lean_dec(v___y_1331_);
v___y_1246_ = v___y_1323_;
v___y_1247_ = v___y_1326_;
v___y_1248_ = v_ictx_1336_;
v___y_1249_ = v___y_1327_;
v___y_1250_ = v___y_1324_;
v___y_1251_ = v___y_1330_;
v___y_1252_ = v_s_1343_;
goto v___jp_1245_;
}
}
}
v___jp_1350_:
{
lean_object* v_fileName_1351_; lean_object* v_fileMap_1352_; lean_object* v_options_1353_; lean_object* v_currNamespace_1354_; lean_object* v_openDecls_1355_; uint8_t v_suppressElabErrors_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; lean_object* v___x_1360_; 
v_fileName_1351_ = lean_ctor_get(v___y_1205_, 0);
v_fileMap_1352_ = lean_ctor_get(v___y_1205_, 1);
v_options_1353_ = lean_ctor_get(v___y_1205_, 2);
v_currNamespace_1354_ = lean_ctor_get(v___y_1205_, 6);
v_openDecls_1355_ = lean_ctor_get(v___y_1205_, 7);
v_suppressElabErrors_1356_ = lean_ctor_get_uint8(v___y_1205_, sizeof(void*)*14 + 1);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = l_Lean_Syntax_getArg(v_docComment_1200_, v___x_1357_);
v___x_1359_ = 1;
v___x_1360_ = l_Lean_Syntax_getPos_x3f(v___x_1358_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1362_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref(v___x_1360_);
v___x_1362_ = l_Lean_Syntax_getTailPos_x3f(v___x_1358_, v___x_1359_);
lean_dec(v___x_1358_);
if (lean_obj_tag(v___x_1362_) == 1)
{
lean_object* v_val_1363_; lean_object* v_source_1364_; lean_object* v___x_1365_; lean_object* v_endPos_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
lean_dec_ref(v___y_1201_);
lean_dec(v_docComment_1200_);
v_val_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1363_);
lean_dec_ref(v___x_1362_);
v_source_1364_ = lean_ctor_get(v_fileMap_1352_, 0);
v___x_1365_ = lean_string_utf8_prev(v_source_1364_, v_val_1363_);
lean_dec(v_val_1363_);
v_endPos_1366_ = lean_string_utf8_prev(v_source_1364_, v___x_1365_);
lean_dec(v___x_1365_);
v___x_1367_ = lean_string_utf8_byte_size(v_source_1364_);
v___x_1368_ = lean_nat_dec_le(v_endPos_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec(v_endPos_1366_);
lean_inc_ref(v_fileName_1351_);
lean_inc(v_currNamespace_1354_);
lean_inc(v_openDecls_1355_);
lean_inc_ref(v_fileMap_1352_);
lean_inc_ref(v_options_1353_);
lean_inc_ref(v_source_1364_);
v___y_1323_ = v_suppressElabErrors_1356_;
v___y_1324_ = v_source_1364_;
v___y_1325_ = v_options_1353_;
v___y_1326_ = v_fileMap_1352_;
v___y_1327_ = v_suppressElabErrors_1356_;
v___y_1328_ = v_openDecls_1355_;
v___y_1329_ = v_currNamespace_1354_;
v___y_1330_ = v_fileName_1351_;
v___y_1331_ = v___x_1357_;
v___y_1332_ = v_val_1361_;
v___y_1333_ = v___x_1367_;
goto v___jp_1322_;
}
else
{
lean_inc_ref(v_fileName_1351_);
lean_inc(v_currNamespace_1354_);
lean_inc(v_openDecls_1355_);
lean_inc_ref(v_fileMap_1352_);
lean_inc_ref(v_options_1353_);
lean_inc_ref(v_source_1364_);
v___y_1323_ = v_suppressElabErrors_1356_;
v___y_1324_ = v_source_1364_;
v___y_1325_ = v_options_1353_;
v___y_1326_ = v_fileMap_1352_;
v___y_1327_ = v_suppressElabErrors_1356_;
v___y_1328_ = v_openDecls_1355_;
v___y_1329_ = v_currNamespace_1354_;
v___y_1330_ = v_fileName_1351_;
v___y_1331_ = v___x_1357_;
v___y_1332_ = v_val_1361_;
v___y_1333_ = v_endPos_1366_;
goto v___jp_1322_;
}
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_dec(v___x_1362_);
lean_dec(v_val_1361_);
v___x_1369_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1370_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1200_, v___x_1369_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v_docComment_1200_);
return v___x_1370_;
}
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v___x_1360_);
lean_dec(v___x_1358_);
v___x_1371_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1372_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1200_, v___x_1371_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v_docComment_1200_);
return v___x_1372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_versoDocString___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1428_, lean_object* v_binders_1429_, lean_object* v_docComment_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1438_; 
lean_inc_ref(v_a_1435_);
lean_inc_ref(v_a_1431_);
v___x_1438_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1455_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1455_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_a_1439_) == 1)
{
lean_object* v_val_1443_; lean_object* v___x_1444_; size_t v_sz_1445_; size_t v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; lean_object* v___x_1450_; 
lean_del_object(v___x_1441_);
v_val_1443_ = lean_ctor_get(v_a_1439_, 0);
lean_inc(v_val_1443_);
lean_dec_ref(v_a_1439_);
v___x_1444_ = l_Lean_Syntax_getArgs(v_val_1443_);
lean_dec(v_val_1443_);
v_sz_1445_ = lean_array_size(v___x_1444_);
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_1445_, v___x_1446_, v___x_1444_);
v___x_1448_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = 0;
v___x_1450_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1428_, v_binders_1429_, v___x_1448_, v___x_1449_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_dec(v_a_1439_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_binders_1429_);
lean_dec(v_declName_1428_);
v___x_1451_ = lean_obj_once(&l_Lean_versoDocString___closed__1, &l_Lean_versoDocString___closed__1_once, _init_l_Lean_versoDocString___closed__1);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1451_);
v___x_1453_ = v___x_1441_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_binders_1429_);
lean_dec(v_declName_1428_);
v_a_1456_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1438_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1438_);
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
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1464_, lean_object* v_binders_1465_, lean_object* v_docComment_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_versoDocString(v_declName_1464_, v_binders_1465_, v_docComment_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1475_, v___x_1476_, v_as_1477_, v_sz_1478_, v_i_1479_, v_b_1480_, v___y_1485_, v___y_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_1489_, lean_object* v___x_1490_, lean_object* v_as_1491_, lean_object* v_sz_1492_, lean_object* v_i_1493_, lean_object* v_b_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1492_);
lean_dec(v_sz_1492_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1493_);
lean_dec(v_i_1493_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_1489_, v___x_1490_, v_as_1491_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v_as_1491_);
lean_dec(v___x_1490_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_1505_, lean_object* v_ref_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1506_, v_msg_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_ref_1517_, lean_object* v_msg_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_1516_, v_ref_1517_, v_msg_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___y_1524_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v_ref_1517_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1527_, lean_object* v_msg_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1537_, lean_object* v_msg_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_1537_, v_msg_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_1547_, lean_object* v_macroStack_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1547_, v_macroStack_1548_, v___y_1553_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_1557_, lean_object* v_macroStack_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_1557_, v_macroStack_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t v_sz_1567_, size_t v_i_1568_, lean_object* v_bs_1569_){
_start:
{
uint8_t v___x_1570_; 
v___x_1570_ = lean_usize_dec_lt(v_i_1568_, v_sz_1567_);
if (v___x_1570_ == 0)
{
return v_bs_1569_;
}
else
{
lean_object* v_v_1571_; lean_object* v___x_1572_; lean_object* v_bs_x27_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v_v_1571_ = lean_array_uget(v_bs_1569_, v_i_1568_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v_bs_x27_1573_ = lean_array_uset(v_bs_1569_, v_i_1568_, v___x_1572_);
v___x_1574_ = ((size_t)1ULL);
v___x_1575_ = lean_usize_add(v_i_1568_, v___x_1574_);
v___x_1576_ = lean_array_uset(v_bs_x27_1573_, v_i_1568_, v_v_1571_);
v_i_1568_ = v___x_1575_;
v_bs_1569_ = v___x_1576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object* v_sz_1578_, lean_object* v_i_1579_, lean_object* v_bs_1580_){
_start:
{
size_t v_sz_boxed_1581_; size_t v_i_boxed_1582_; lean_object* v_res_1583_; 
v_sz_boxed_1581_ = lean_unbox_usize(v_sz_1578_);
lean_dec(v_sz_1578_);
v_i_boxed_1582_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_res_1583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_1581_, v_i_boxed_1582_, v_bs_1580_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1584_, lean_object* v_doc_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1601_; lean_object* v_env_1608_; lean_object* v___x_1609_; lean_object* v_terminalNesting_1610_; 
v___x_1593_ = lean_st_ref_get(v_a_1591_);
v_env_1608_ = lean_ctor_get(v___x_1593_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1593_);
v___x_1609_ = l_Lean_getMainVersoModuleDocs(v_env_1608_);
v_terminalNesting_1610_ = lean_ctor_get(v___x_1609_, 1);
lean_inc(v_terminalNesting_1610_);
lean_dec_ref(v___x_1609_);
if (lean_obj_tag(v_terminalNesting_1610_) == 0)
{
v___y_1601_ = v_terminalNesting_1610_;
goto v___jp_1600_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v_val_1611_ = lean_ctor_get(v_terminalNesting_1610_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_terminalNesting_1610_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1613_ = v_terminalNesting_1610_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v_terminalNesting_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_val_1611_, v___x_1615_);
lean_dec(v_val_1611_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
v___y_1601_ = v___x_1618_;
goto v___jp_1600_;
}
}
}
v___jp_1594_:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1597_, 0, v_range_1584_);
lean_closure_set(v___x_1597_, 1, v___y_1595_);
lean_closure_set(v___x_1597_, 2, v___y_1596_);
v___x_1598_ = 0;
v___x_1599_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1597_, v___x_1598_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
return v___x_1599_;
}
v___jp_1600_:
{
lean_object* v___x_1602_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = l_Lean_Syntax_getArgs(v_doc_1585_);
v_sz_1603_ = lean_array_size(v___x_1602_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_1603_, v___x_1604_, v___x_1602_);
if (lean_obj_tag(v___y_1601_) == 0)
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___y_1595_ = v___x_1605_;
v___y_1596_ = v___x_1606_;
goto v___jp_1594_;
}
else
{
lean_object* v_val_1607_; 
v_val_1607_ = lean_ctor_get(v___y_1601_, 0);
lean_inc(v_val_1607_);
lean_dec_ref(v___y_1601_);
v___y_1595_ = v___x_1605_;
v___y_1596_ = v_val_1607_;
goto v___jp_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1621_, lean_object* v_doc_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_versoModDocString(v_range_1621_, v_doc_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_);
lean_dec(v_doc_1622_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object* v___x_1631_, lean_object* v_declName_1632_, lean_object* v___x_1633_, lean_object* v___x_1634_, uint8_t v___x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_fileName_1643_; lean_object* v_options_1644_; lean_object* v_currRecDepth_1645_; lean_object* v_maxRecDepth_1646_; lean_object* v_ref_1647_; lean_object* v_currNamespace_1648_; lean_object* v_openDecls_1649_; lean_object* v_initHeartbeats_1650_; lean_object* v_maxHeartbeats_1651_; lean_object* v_quotContext_1652_; lean_object* v_currMacroScope_1653_; uint8_t v_diag_1654_; lean_object* v_cancelTk_x3f_1655_; uint8_t v_suppressElabErrors_1656_; lean_object* v_inheritedTraceOptions_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
v_fileName_1643_ = lean_ctor_get(v___y_1640_, 0);
v_options_1644_ = lean_ctor_get(v___y_1640_, 2);
v_currRecDepth_1645_ = lean_ctor_get(v___y_1640_, 3);
v_maxRecDepth_1646_ = lean_ctor_get(v___y_1640_, 4);
v_ref_1647_ = lean_ctor_get(v___y_1640_, 5);
v_currNamespace_1648_ = lean_ctor_get(v___y_1640_, 6);
v_openDecls_1649_ = lean_ctor_get(v___y_1640_, 7);
v_initHeartbeats_1650_ = lean_ctor_get(v___y_1640_, 8);
v_maxHeartbeats_1651_ = lean_ctor_get(v___y_1640_, 9);
v_quotContext_1652_ = lean_ctor_get(v___y_1640_, 10);
v_currMacroScope_1653_ = lean_ctor_get(v___y_1640_, 11);
v_diag_1654_ = lean_ctor_get_uint8(v___y_1640_, sizeof(void*)*14);
v_cancelTk_x3f_1655_ = lean_ctor_get(v___y_1640_, 12);
v_suppressElabErrors_1656_ = lean_ctor_get_uint8(v___y_1640_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1657_ = lean_ctor_get(v___y_1640_, 13);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___y_1640_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___y_1640_, 1);
lean_dec(v_unused_1666_);
v___x_1659_ = v___y_1640_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_inheritedTraceOptions_1657_);
lean_inc(v_cancelTk_x3f_1655_);
lean_inc(v_currMacroScope_1653_);
lean_inc(v_quotContext_1652_);
lean_inc(v_maxHeartbeats_1651_);
lean_inc(v_initHeartbeats_1650_);
lean_inc(v_openDecls_1649_);
lean_inc(v_currNamespace_1648_);
lean_inc(v_ref_1647_);
lean_inc(v_maxRecDepth_1646_);
lean_inc(v_currRecDepth_1645_);
lean_inc(v_options_1644_);
lean_inc(v_fileName_1643_);
lean_dec(v___y_1640_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1631_);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_fileName_1643_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_options_1644_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_currRecDepth_1645_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_maxRecDepth_1646_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v_ref_1647_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_currNamespace_1648_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_openDecls_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_initHeartbeats_1650_);
lean_ctor_set(v_reuseFailAlloc_1664_, 9, v_maxHeartbeats_1651_);
lean_ctor_set(v_reuseFailAlloc_1664_, 10, v_quotContext_1652_);
lean_ctor_set(v_reuseFailAlloc_1664_, 11, v_currMacroScope_1653_);
lean_ctor_set(v_reuseFailAlloc_1664_, 12, v_cancelTk_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1664_, 13, v_inheritedTraceOptions_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*14, v_diag_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*14 + 1, v_suppressElabErrors_1656_);
v___x_1662_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1632_, v___x_1633_, v___x_1634_, v___x_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___x_1662_, v___y_1641_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object* v___x_1667_, lean_object* v_declName_1668_, lean_object* v___x_1669_, lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v___x_17179__boxed_1679_; lean_object* v_res_1680_; 
v___x_17179__boxed_1679_ = lean_unbox(v___x_1671_);
v_res_1680_ = l_Lean_versoDocStringFromString___lam__0(v___x_1667_, v_declName_1668_, v___x_1669_, v___x_1670_, v___x_17179__boxed_1679_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t v___y_1681_, uint8_t v_suppressElabErrors_1682_, lean_object* v_x_1683_){
_start:
{
if (lean_obj_tag(v_x_1683_) == 1)
{
lean_object* v_pre_1684_; 
v_pre_1684_ = lean_ctor_get(v_x_1683_, 0);
switch(lean_obj_tag(v_pre_1684_))
{
case 1:
{
lean_object* v_pre_1685_; 
v_pre_1685_ = lean_ctor_get(v_pre_1684_, 0);
switch(lean_obj_tag(v_pre_1685_))
{
case 0:
{
lean_object* v_str_1686_; lean_object* v_str_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v_str_1686_ = lean_ctor_get(v_x_1683_, 1);
v_str_1687_ = lean_ctor_get(v_pre_1684_, 1);
v___x_1688_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_1689_ = lean_string_dec_eq(v_str_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_1691_ = lean_string_dec_eq(v_str_1687_, v___x_1690_);
if (v___x_1691_ == 0)
{
return v___y_1681_;
}
else
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_1693_ = lean_string_dec_eq(v_str_1686_, v___x_1692_);
if (v___x_1693_ == 0)
{
return v___y_1681_;
}
else
{
return v_suppressElabErrors_1682_;
}
}
}
else
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_1695_ = lean_string_dec_eq(v_str_1686_, v___x_1694_);
if (v___x_1695_ == 0)
{
return v___y_1681_;
}
else
{
return v_suppressElabErrors_1682_;
}
}
}
case 1:
{
lean_object* v_pre_1696_; 
v_pre_1696_ = lean_ctor_get(v_pre_1685_, 0);
if (lean_obj_tag(v_pre_1696_) == 0)
{
lean_object* v_str_1697_; lean_object* v_str_1698_; lean_object* v_str_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_str_1697_ = lean_ctor_get(v_x_1683_, 1);
v_str_1698_ = lean_ctor_get(v_pre_1684_, 1);
v_str_1699_ = lean_ctor_get(v_pre_1685_, 1);
v___x_1700_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_1701_ = lean_string_dec_eq(v_str_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
return v___y_1681_;
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_1703_ = lean_string_dec_eq(v_str_1698_, v___x_1702_);
if (v___x_1703_ == 0)
{
return v___y_1681_;
}
else
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_1705_ = lean_string_dec_eq(v_str_1697_, v___x_1704_);
if (v___x_1705_ == 0)
{
return v___y_1681_;
}
else
{
return v_suppressElabErrors_1682_;
}
}
}
}
else
{
return v___y_1681_;
}
}
default: 
{
return v___y_1681_;
}
}
}
case 0:
{
lean_object* v_str_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_str_1706_ = lean_ctor_get(v_x_1683_, 1);
v___x_1707_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_1708_ = lean_string_dec_eq(v_str_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
return v___y_1681_;
}
else
{
return v_suppressElabErrors_1682_;
}
}
default: 
{
return v___y_1681_;
}
}
}
else
{
return v___y_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object* v___y_1709_, lean_object* v_suppressElabErrors_1710_, lean_object* v_x_1711_){
_start:
{
uint8_t v___y_17235__boxed_1712_; uint8_t v_suppressElabErrors_boxed_1713_; uint8_t v_res_1714_; lean_object* v_r_1715_; 
v___y_17235__boxed_1712_ = lean_unbox(v___y_1709_);
v_suppressElabErrors_boxed_1713_ = lean_unbox(v_suppressElabErrors_1710_);
v_res_1714_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(v___y_17235__boxed_1712_, v_suppressElabErrors_boxed_1713_, v_x_1711_);
lean_dec(v_x_1711_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object* v_ref_1716_, lean_object* v_msgData_1717_, uint8_t v_severity_1718_, uint8_t v_isSilent_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; uint8_t v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1762_; uint8_t v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; uint8_t v___y_1767_; uint8_t v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1787_; uint8_t v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; uint8_t v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1798_; uint8_t v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; uint8_t v___y_1804_; uint8_t v___x_1809_; uint8_t v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; uint8_t v___y_1816_; uint8_t v___y_1817_; uint8_t v___y_1819_; uint8_t v___x_1834_; 
v___x_1809_ = 2;
v___x_1834_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1718_, v___x_1809_);
if (v___x_1834_ == 0)
{
v___y_1819_ = v___x_1834_;
goto v___jp_1818_;
}
else
{
uint8_t v___x_1835_; 
lean_inc_ref(v_msgData_1717_);
v___x_1835_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1717_);
v___y_1819_ = v___x_1835_;
goto v___jp_1818_;
}
v___jp_1725_:
{
lean_object* v___x_1735_; lean_object* v_currNamespace_1736_; lean_object* v_openDecls_1737_; lean_object* v_env_1738_; lean_object* v_nextMacroScope_1739_; lean_object* v_ngen_1740_; lean_object* v_auxDeclNGen_1741_; lean_object* v_traceState_1742_; lean_object* v_cache_1743_; lean_object* v_messages_1744_; lean_object* v_infoState_1745_; lean_object* v_snapshotTasks_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1760_; 
v___x_1735_ = lean_st_ref_take(v___y_1734_);
v_currNamespace_1736_ = lean_ctor_get(v___y_1733_, 6);
lean_inc(v_currNamespace_1736_);
v_openDecls_1737_ = lean_ctor_get(v___y_1733_, 7);
lean_inc(v_openDecls_1737_);
lean_dec_ref(v___y_1733_);
v_env_1738_ = lean_ctor_get(v___x_1735_, 0);
v_nextMacroScope_1739_ = lean_ctor_get(v___x_1735_, 1);
v_ngen_1740_ = lean_ctor_get(v___x_1735_, 2);
v_auxDeclNGen_1741_ = lean_ctor_get(v___x_1735_, 3);
v_traceState_1742_ = lean_ctor_get(v___x_1735_, 4);
v_cache_1743_ = lean_ctor_get(v___x_1735_, 5);
v_messages_1744_ = lean_ctor_get(v___x_1735_, 6);
v_infoState_1745_ = lean_ctor_get(v___x_1735_, 7);
v_snapshotTasks_1746_ = lean_ctor_get(v___x_1735_, 8);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1748_ = v___x_1735_;
v_isShared_1749_ = v_isSharedCheck_1760_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snapshotTasks_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_messages_1744_);
lean_inc(v_cache_1743_);
lean_inc(v_traceState_1742_);
lean_inc(v_auxDeclNGen_1741_);
lean_inc(v_ngen_1740_);
lean_inc(v_nextMacroScope_1739_);
lean_inc(v_env_1738_);
lean_dec(v___x_1735_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1760_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_currNamespace_1736_);
lean_ctor_set(v___x_1750_, 1, v_openDecls_1737_);
v___x_1751_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___y_1726_);
v___x_1752_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1752_, 0, v___y_1727_);
lean_ctor_set(v___x_1752_, 1, v___y_1732_);
lean_ctor_set(v___x_1752_, 2, v___y_1730_);
lean_ctor_set(v___x_1752_, 3, v___y_1731_);
lean_ctor_set(v___x_1752_, 4, v___x_1751_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*5, v___y_1729_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*5 + 1, v___y_1728_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*5 + 2, v_isSilent_1719_);
v___x_1753_ = l_Lean_MessageLog_add(v___x_1752_, v_messages_1744_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 6, v___x_1753_);
v___x_1755_ = v___x_1748_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_env_1738_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_nextMacroScope_1739_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_ngen_1740_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_auxDeclNGen_1741_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_traceState_1742_);
lean_ctor_set(v_reuseFailAlloc_1759_, 5, v_cache_1743_);
lean_ctor_set(v_reuseFailAlloc_1759_, 6, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1759_, 7, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 8, v_snapshotTasks_1746_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_st_ref_set(v___y_1734_, v___x_1755_);
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
v___jp_1761_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1785_; 
v___x_1770_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1717_);
v___x_1771_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_1770_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1785_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1785_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_inc_ref(v___y_1764_);
v___x_1776_ = l_Lean_FileMap_toPosition(v___y_1764_, v___y_1766_);
lean_dec(v___y_1766_);
v___x_1777_ = l_Lean_FileMap_toPosition(v___y_1764_, v___y_1769_);
lean_dec(v___y_1769_);
v___x_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
v___x_1779_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1763_ == 0)
{
lean_del_object(v___x_1774_);
lean_dec_ref(v___y_1762_);
v___y_1726_ = v_a_1772_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1768_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___x_1778_;
v___y_1731_ = v___x_1779_;
v___y_1732_ = v___x_1776_;
v___y_1733_ = v___y_1722_;
v___y_1734_ = v___y_1723_;
goto v___jp_1725_;
}
else
{
uint8_t v___x_1780_; 
lean_inc(v_a_1772_);
v___x_1780_ = l_Lean_MessageData_hasTag(v___y_1762_, v_a_1772_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec_ref(v___x_1778_);
lean_dec_ref(v___x_1776_);
lean_dec(v_a_1772_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1722_);
v___x_1781_ = lean_box(0);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1781_);
v___x_1783_ = v___x_1774_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
else
{
lean_del_object(v___x_1774_);
v___y_1726_ = v_a_1772_;
v___y_1727_ = v___y_1765_;
v___y_1728_ = v___y_1768_;
v___y_1729_ = v___y_1767_;
v___y_1730_ = v___x_1778_;
v___y_1731_ = v___x_1779_;
v___y_1732_ = v___x_1776_;
v___y_1733_ = v___y_1722_;
v___y_1734_ = v___y_1723_;
goto v___jp_1725_;
}
}
}
}
v___jp_1786_:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Syntax_getTailPos_x3f(v___y_1793_, v___y_1792_);
lean_dec(v___y_1793_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_inc(v___y_1794_);
v___y_1762_ = v___y_1787_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1789_;
v___y_1765_ = v___y_1790_;
v___y_1766_ = v___y_1794_;
v___y_1767_ = v___y_1792_;
v___y_1768_ = v___y_1791_;
v___y_1769_ = v___y_1794_;
goto v___jp_1761_;
}
else
{
lean_object* v_val_1796_; 
v_val_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_val_1796_);
lean_dec_ref(v___x_1795_);
v___y_1762_ = v___y_1787_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1789_;
v___y_1765_ = v___y_1790_;
v___y_1766_ = v___y_1794_;
v___y_1767_ = v___y_1792_;
v___y_1768_ = v___y_1791_;
v___y_1769_ = v_val_1796_;
goto v___jp_1761_;
}
}
v___jp_1797_:
{
lean_object* v_ref_1805_; lean_object* v___x_1806_; 
v_ref_1805_ = l_Lean_replaceRef(v_ref_1716_, v___y_1801_);
lean_dec(v___y_1801_);
v___x_1806_ = l_Lean_Syntax_getPos_x3f(v_ref_1805_, v___y_1803_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___y_1787_ = v___y_1798_;
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1800_;
v___y_1790_ = v___y_1802_;
v___y_1791_ = v___y_1804_;
v___y_1792_ = v___y_1803_;
v___y_1793_ = v_ref_1805_;
v___y_1794_ = v___x_1807_;
goto v___jp_1786_;
}
else
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v___x_1806_);
v___y_1787_ = v___y_1798_;
v___y_1788_ = v___y_1799_;
v___y_1789_ = v___y_1800_;
v___y_1790_ = v___y_1802_;
v___y_1791_ = v___y_1804_;
v___y_1792_ = v___y_1803_;
v___y_1793_ = v_ref_1805_;
v___y_1794_ = v_val_1808_;
goto v___jp_1786_;
}
}
v___jp_1810_:
{
if (v___y_1817_ == 0)
{
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1812_;
v___y_1801_ = v___y_1813_;
v___y_1802_ = v___y_1814_;
v___y_1803_ = v___y_1816_;
v___y_1804_ = v_severity_1718_;
goto v___jp_1797_;
}
else
{
v___y_1798_ = v___y_1815_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1812_;
v___y_1801_ = v___y_1813_;
v___y_1802_ = v___y_1814_;
v___y_1803_ = v___y_1816_;
v___y_1804_ = v___x_1809_;
goto v___jp_1797_;
}
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
lean_object* v_fileName_1820_; lean_object* v_fileMap_1821_; lean_object* v_options_1822_; lean_object* v_ref_1823_; uint8_t v_suppressElabErrors_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___f_1827_; uint8_t v___x_1828_; uint8_t v___x_1829_; 
v_fileName_1820_ = lean_ctor_get(v___y_1722_, 0);
v_fileMap_1821_ = lean_ctor_get(v___y_1722_, 1);
v_options_1822_ = lean_ctor_get(v___y_1722_, 2);
v_ref_1823_ = lean_ctor_get(v___y_1722_, 5);
v_suppressElabErrors_1824_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*14 + 1);
v___x_1825_ = lean_box(v___y_1819_);
v___x_1826_ = lean_box(v_suppressElabErrors_1824_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1827_, 0, v___x_1825_);
lean_closure_set(v___f_1827_, 1, v___x_1826_);
v___x_1828_ = 1;
v___x_1829_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1718_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_inc_ref(v_fileName_1820_);
lean_inc(v_ref_1823_);
lean_inc_ref(v_fileMap_1821_);
v___y_1811_ = v_suppressElabErrors_1824_;
v___y_1812_ = v_fileMap_1821_;
v___y_1813_ = v_ref_1823_;
v___y_1814_ = v_fileName_1820_;
v___y_1815_ = v___f_1827_;
v___y_1816_ = v___y_1819_;
v___y_1817_ = v___x_1829_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = l_Lean_warningAsError;
v___x_1831_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1822_, v___x_1830_);
lean_inc_ref(v_fileName_1820_);
lean_inc(v_ref_1823_);
lean_inc_ref(v_fileMap_1821_);
v___y_1811_ = v_suppressElabErrors_1824_;
v___y_1812_ = v_fileMap_1821_;
v___y_1813_ = v_ref_1823_;
v___y_1814_ = v_fileName_1820_;
v___y_1815_ = v___f_1827_;
v___y_1816_ = v___y_1819_;
v___y_1817_ = v___x_1831_;
goto v___jp_1810_;
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v___y_1722_);
lean_dec_ref(v_msgData_1717_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object* v_ref_1836_, lean_object* v_msgData_1837_, lean_object* v_severity_1838_, lean_object* v_isSilent_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
uint8_t v_severity_boxed_1845_; uint8_t v_isSilent_boxed_1846_; lean_object* v_res_1847_; 
v_severity_boxed_1845_ = lean_unbox(v_severity_1838_);
v_isSilent_boxed_1846_ = lean_unbox(v_isSilent_1839_);
v_res_1847_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1836_, v_msgData_1837_, v_severity_boxed_1845_, v_isSilent_boxed_1846_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v_ref_1836_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object* v_as_1848_, size_t v_sz_1849_, size_t v_i_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_usize_dec_lt(v_i_1850_, v_sz_1849_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v___y_1856_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_b_1851_);
return v___x_1860_;
}
else
{
lean_object* v_ref_1861_; lean_object* v_a_1862_; uint8_t v_severity_1863_; lean_object* v_data_1864_; uint8_t v___x_1865_; lean_object* v___x_1866_; 
v_ref_1861_ = lean_ctor_get(v___y_1856_, 5);
v_a_1862_ = lean_array_uget_borrowed(v_as_1848_, v_i_1850_);
v_severity_1863_ = lean_ctor_get_uint8(v_a_1862_, sizeof(void*)*5 + 1);
v_data_1864_ = lean_ctor_get(v_a_1862_, 4);
v___x_1865_ = 0;
lean_inc_ref(v___y_1856_);
lean_inc(v_data_1864_);
v___x_1866_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1861_, v_data_1864_, v_severity_1863_, v___x_1865_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; 
lean_dec_ref(v___x_1866_);
v___x_1867_ = lean_box(0);
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_i_1850_, v___x_1868_);
v_i_1850_ = v___x_1869_;
v_b_1851_ = v___x_1867_;
goto _start;
}
else
{
lean_dec_ref(v___y_1856_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object* v_as_1871_, lean_object* v_sz_1872_, lean_object* v_i_1873_, lean_object* v_b_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
size_t v_sz_boxed_1882_; size_t v_i_boxed_1883_; lean_object* v_res_1884_; 
v_sz_boxed_1882_ = lean_unbox_usize(v_sz_1872_);
lean_dec(v_sz_1872_);
v_i_boxed_1883_ = lean_unbox_usize(v_i_1873_);
lean_dec(v_i_1873_);
v_res_1884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_1871_, v_sz_boxed_1882_, v_i_boxed_1883_, v_b_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v_as_1871_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t v_flag_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v_infoState_1889_; lean_object* v_env_1890_; lean_object* v_nextMacroScope_1891_; lean_object* v_ngen_1892_; lean_object* v_auxDeclNGen_1893_; lean_object* v_traceState_1894_; lean_object* v_cache_1895_; lean_object* v_messages_1896_; lean_object* v_snapshotTasks_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1917_; 
v___x_1888_ = lean_st_ref_take(v___y_1886_);
v_infoState_1889_ = lean_ctor_get(v___x_1888_, 7);
v_env_1890_ = lean_ctor_get(v___x_1888_, 0);
v_nextMacroScope_1891_ = lean_ctor_get(v___x_1888_, 1);
v_ngen_1892_ = lean_ctor_get(v___x_1888_, 2);
v_auxDeclNGen_1893_ = lean_ctor_get(v___x_1888_, 3);
v_traceState_1894_ = lean_ctor_get(v___x_1888_, 4);
v_cache_1895_ = lean_ctor_get(v___x_1888_, 5);
v_messages_1896_ = lean_ctor_get(v___x_1888_, 6);
v_snapshotTasks_1897_ = lean_ctor_get(v___x_1888_, 8);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snapshotTasks_1897_);
lean_inc(v_infoState_1889_);
lean_inc(v_messages_1896_);
lean_inc(v_cache_1895_);
lean_inc(v_traceState_1894_);
lean_inc(v_auxDeclNGen_1893_);
lean_inc(v_ngen_1892_);
lean_inc(v_nextMacroScope_1891_);
lean_inc(v_env_1890_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1917_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_assignment_1901_; lean_object* v_lazyAssignment_1902_; lean_object* v_trees_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1916_; 
v_assignment_1901_ = lean_ctor_get(v_infoState_1889_, 0);
v_lazyAssignment_1902_ = lean_ctor_get(v_infoState_1889_, 1);
v_trees_1903_ = lean_ctor_get(v_infoState_1889_, 2);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_infoState_1889_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1905_ = v_infoState_1889_;
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_trees_1903_);
lean_inc(v_lazyAssignment_1902_);
lean_inc(v_assignment_1901_);
lean_dec(v_infoState_1889_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_assignment_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_lazyAssignment_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_trees_1903_);
v___x_1908_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*3, v_flag_1885_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 7, v___x_1908_);
v___x_1910_ = v___x_1899_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_env_1890_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_nextMacroScope_1891_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_ngen_1892_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_auxDeclNGen_1893_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_traceState_1894_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_cache_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_messages_1896_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1914_, 8, v_snapshotTasks_1897_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_st_ref_set(v___y_1886_, v___x_1910_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object* v_flag_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v_flag_boxed_1921_; lean_object* v_res_1922_; 
v_flag_boxed_1921_ = lean_unbox(v_flag_1918_);
v_res_1922_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_1921_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t v_flag_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; lean_object* v_infoState_1933_; uint8_t v_enabled_1934_; lean_object* v_a_1936_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1932_ = lean_st_ref_get(v___y_1930_);
v_infoState_1933_ = lean_ctor_get(v___x_1932_, 7);
lean_inc_ref(v_infoState_1933_);
lean_dec(v___x_1932_);
v_enabled_1934_ = lean_ctor_get_uint8(v_infoState_1933_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1933_);
v___x_1946_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_1923_, v___y_1930_);
lean_dec_ref(v___x_1946_);
lean_inc(v___y_1930_);
v___x_1947_ = lean_apply_7(v_x_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, lean_box(0));
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
v___x_1949_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1934_, v___y_1930_);
lean_dec(v___y_1930_);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1949_, 0);
lean_dec(v_unused_1957_);
v___x_1951_ = v___x_1949_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v___x_1949_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1948_);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1948_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1947_);
v_a_1936_ = v_a_1958_;
goto v___jp_1935_;
}
v___jp_1935_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v___x_1937_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1934_, v___y_1930_);
lean_dec(v___y_1930_);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1945_);
v___x_1939_ = v___x_1937_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 1);
lean_ctor_set(v___x_1939_, 0, v_a_1936_);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1936_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object* v_flag_1959_, lean_object* v_x_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
uint8_t v_flag_boxed_1968_; lean_object* v_res_1969_; 
v_flag_boxed_1968_ = lean_unbox(v_flag_1959_);
v_res_1969_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_boxed_1968_, v_x_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object* v_msgData_1970_, uint8_t v_severity_1971_, uint8_t v_isSilent_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_ref_1980_; lean_object* v___x_1981_; 
v_ref_1980_ = lean_ctor_get(v___y_1977_, 5);
lean_inc(v_ref_1980_);
v___x_1981_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1980_, v_msgData_1970_, v_severity_1971_, v_isSilent_1972_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v_ref_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object* v_msgData_1982_, lean_object* v_severity_1983_, lean_object* v_isSilent_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v_severity_boxed_1992_; uint8_t v_isSilent_boxed_1993_; lean_object* v_res_1994_; 
v_severity_boxed_1992_ = lean_unbox(v_severity_1983_);
v_isSilent_boxed_1993_ = lean_unbox(v_isSilent_1984_);
v_res_1994_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1982_, v_severity_boxed_1992_, v_isSilent_boxed_1993_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object* v_msgData_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = 2;
v___x_2004_ = 0;
v___x_2005_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1995_, v___x_2003_, v___x_2004_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object* v_msgData_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v_msgData_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object* v_as_2015_, size_t v_sz_2016_, size_t v_i_2017_, lean_object* v_b_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2017_, v_sz_2016_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec_ref(v___y_2023_);
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2018_);
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; lean_object* v_snd_2029_; lean_object* v_snd_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_a_2028_ = lean_array_uget_borrowed(v_as_2015_, v_i_2017_);
v_snd_2029_ = lean_ctor_get(v_a_2028_, 1);
v_snd_2030_ = lean_ctor_get(v_snd_2029_, 1);
lean_inc(v_snd_2030_);
v___x_2031_ = l_Lean_Parser_Error_toString(v_snd_2030_);
v___x_2032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
v___x_2033_ = l_Lean_MessageData_ofFormat(v___x_2032_);
lean_inc_ref(v___y_2023_);
v___x_2034_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2033_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; size_t v___x_2036_; size_t v___x_2037_; 
lean_dec_ref(v___x_2034_);
v___x_2035_ = lean_box(0);
v___x_2036_ = ((size_t)1ULL);
v___x_2037_ = lean_usize_add(v_i_2017_, v___x_2036_);
v_i_2017_ = v___x_2037_;
v_b_2018_ = v___x_2035_;
goto _start;
}
else
{
lean_dec_ref(v___y_2023_);
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object* v_as_2039_, lean_object* v_sz_2040_, lean_object* v_i_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
size_t v_sz_boxed_2050_; size_t v_i_boxed_2051_; lean_object* v_res_2052_; 
v_sz_boxed_2050_ = lean_unbox_usize(v_sz_2040_);
lean_dec(v_sz_2040_);
v_i_boxed_2051_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_2039_, v_sz_boxed_2050_, v_i_boxed_2051_, v_b_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v_as_2039_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2072_, lean_object* v_docComment_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v_env_2082_; lean_object* v_fileName_2083_; lean_object* v_options_2084_; lean_object* v_currNamespace_2085_; lean_object* v_openDecls_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2081_ = lean_st_ref_get(v_a_2079_);
v_env_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc_ref(v_env_2082_);
lean_dec(v___x_2081_);
v_fileName_2083_ = lean_ctor_get(v_a_2078_, 0);
v_options_2084_ = lean_ctor_get(v_a_2078_, 2);
v_currNamespace_2085_ = lean_ctor_get(v_a_2078_, 6);
v_openDecls_2086_ = lean_ctor_get(v_a_2078_, 7);
v___x_2087_ = lean_string_utf8_byte_size(v_docComment_2073_);
lean_inc_ref(v_docComment_2073_);
v___x_2088_ = l_Lean_FileMap_ofString(v_docComment_2073_);
lean_inc_ref(v___x_2088_);
lean_inc_ref(v_fileName_2083_);
lean_inc_ref(v_docComment_2073_);
v___x_2089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2089_, 0, v_docComment_2073_);
lean_ctor_set(v___x_2089_, 1, v_fileName_2083_);
lean_ctor_set(v___x_2089_, 2, v___x_2088_);
lean_ctor_set(v___x_2089_, 3, v___x_2087_);
lean_inc(v_openDecls_2086_);
lean_inc(v_currNamespace_2085_);
lean_inc_ref(v_options_2084_);
lean_inc_ref(v_env_2082_);
v___x_2090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2090_, 0, v_env_2082_);
lean_ctor_set(v___x_2090_, 1, v_options_2084_);
lean_ctor_set(v___x_2090_, 2, v_currNamespace_2085_);
lean_ctor_set(v___x_2090_, 3, v_openDecls_2086_);
v___x_2091_ = l_Lean_Parser_mkParserState(v_docComment_2073_);
lean_dec_ref(v_docComment_2073_);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__2));
v___x_2094_ = l_Lean_Parser_getTokenTable(v_env_2082_);
v___x_2095_ = l_Lean_Parser_ParserFn_run(v___x_2093_, v___x_2089_, v___x_2090_, v___x_2094_, v___x_2091_);
lean_inc_ref(v___x_2095_);
v___x_2096_ = l_Lean_Parser_ParserState_allErrors(v___x_2095_);
v___x_2097_ = lean_array_get_size(v___x_2096_);
v___x_2098_ = lean_nat_dec_eq(v___x_2097_, v___x_2092_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; size_t v_sz_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v___x_2088_);
lean_dec(v_declName_2072_);
v___x_2099_ = lean_box(0);
v_sz_2100_ = lean_array_size(v___x_2096_);
v___x_2101_ = ((size_t)0ULL);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_2096_, v_sz_2100_, v___x_2101_, v___x_2099_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec_ref(v___x_2096_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2110_; 
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v___x_2102_, 0);
lean_dec(v_unused_2111_);
v___x_2104_ = v___x_2102_;
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
else
{
lean_dec(v___x_2102_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2110_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2106_ = lean_obj_once(&l_Lean_versoDocString___closed__1, &l_Lean_versoDocString___closed__1_once, _init_l_Lean_versoDocString___closed__1);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 0, v___x_2106_);
v___x_2108_ = v___x_2104_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2102_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2102_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v___x_2120_; 
lean_dec_ref(v___x_2096_);
v___x_2120_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2079_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_a_2123_; lean_object* v_stxStack_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; size_t v_sz_2146_; size_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v_stxStack_2141_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_ref(v_stxStack_2141_);
lean_dec_ref(v___x_2095_);
v___x_2142_ = 0;
v___x_2143_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2141_);
lean_dec_ref(v_stxStack_2141_);
v___x_2144_ = l_Lean_Syntax_getArgs(v___x_2143_);
lean_dec(v___x_2143_);
v___x_2145_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__6));
v_sz_2146_ = lean_array_size(v___x_2144_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_2146_, v___x_2147_, v___x_2144_);
v___x_2149_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2149_, 0, v___x_2148_);
v___x_2150_ = 1;
v___x_2151_ = lean_box(v___x_2150_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_versoDocStringFromString___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2152_, 0, v___x_2088_);
lean_closure_set(v___f_2152_, 1, v_declName_2072_);
lean_closure_set(v___f_2152_, 2, v___x_2145_);
lean_closure_set(v___f_2152_, 3, v___x_2149_);
lean_closure_set(v___f_2152_, 4, v___x_2151_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
v___x_2153_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_2142_, v___f_2152_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2079_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l_Lean_Core_setMessageLog___redArg(v_a_2121_, v_a_2079_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v___x_2158_; lean_object* v___x_2159_; size_t v_sz_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___x_2157_);
v___x_2158_ = l_Lean_MessageLog_toArray(v_a_2156_);
lean_dec(v_a_2156_);
v___x_2159_ = lean_box(0);
v_sz_2160_ = lean_array_size(v___x_2158_);
v___x_2161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_2158_, v_sz_2160_, v___x_2147_, v___x_2159_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec_ref(v___x_2158_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2161_, 0);
lean_dec(v_unused_2169_);
v___x_2163_ = v___x_2161_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2161_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v_a_2154_);
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2154_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_a_2154_);
v_a_2170_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2161_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2161_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2156_);
lean_dec(v_a_2154_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
v_a_2178_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2157_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2157_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; 
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
v_a_2186_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2186_);
lean_dec_ref(v___x_2155_);
v_a_2123_ = v_a_2186_;
goto v___jp_2122_;
}
}
else
{
lean_object* v_a_2187_; 
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
v_a_2187_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2153_);
v_a_2123_ = v_a_2187_;
goto v___jp_2122_;
}
v___jp_2122_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Core_setMessageLog___redArg(v_a_2121_, v_a_2079_);
lean_dec(v_a_2079_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2124_, 0);
lean_dec(v_unused_2132_);
v___x_2126_ = v___x_2124_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_dec(v___x_2124_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 1);
lean_ctor_set(v___x_2126_, 0, v_a_2123_);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2123_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_a_2123_);
v_a_2133_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2124_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2124_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v___x_2088_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_declName_2072_);
v_a_2188_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2120_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2120_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2196_, lean_object* v_docComment_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_versoDocStringFromString(v_declName_2196_, v_docComment_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t v_flag_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_2206_, v___y_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object* v_flag_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_flag_boxed_2223_; lean_object* v_res_2224_; 
v_flag_boxed_2223_ = lean_unbox(v_flag_2215_);
v_res_2224_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_2223_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object* v_00_u03b1_2225_, uint8_t v_flag_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_2226_, v_x_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_flag_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
uint8_t v_flag_boxed_2246_; lean_object* v_res_2247_; 
v_flag_boxed_2246_ = lean_unbox(v_flag_2237_);
v_res_2247_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(v_00_u03b1_2236_, v_flag_boxed_2246_, v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object* v_ref_2248_, lean_object* v_msgData_2249_, uint8_t v_severity_2250_, uint8_t v_isSilent_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2248_, v_msgData_2249_, v_severity_2250_, v_isSilent_2251_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object* v_ref_2260_, lean_object* v_msgData_2261_, lean_object* v_severity_2262_, lean_object* v_isSilent_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
uint8_t v_severity_boxed_2271_; uint8_t v_isSilent_boxed_2272_; lean_object* v_res_2273_; 
v_severity_boxed_2271_ = lean_unbox(v_severity_2262_);
v_isSilent_boxed_2272_ = lean_unbox(v_isSilent_2263_);
v_res_2273_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(v_ref_2260_, v_msgData_2261_, v_severity_boxed_2271_, v_isSilent_boxed_2272_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_ref_2260_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2274_, lean_object* v_declName_2275_, lean_object* v_env_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = l_Lean_docStringExt;
v___x_2278_ = l_String_removeLeadingSpaces(v_docString_2274_);
v___x_2279_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2277_, v_env_2276_, v_declName_2275_, v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2280_, lean_object* v_modifyEnv_2281_, lean_object* v_docString_2282_){
_start:
{
lean_object* v___f_2283_; lean_object* v___x_2284_; 
v___f_2283_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2283_, 0, v_docString_2282_);
lean_closure_set(v___f_2283_, 1, v_declName_2280_);
v___x_2284_ = lean_apply_1(v_modifyEnv_2281_, v___f_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_docComment_2287_, lean_object* v_toBind_2288_, lean_object* v___f_2289_, lean_object* v_____r_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = l_Lean_getDocStringText___redArg(v_inst_2285_, v_inst_2286_, v_docComment_2287_);
v___x_2292_ = lean_apply_4(v_toBind_2288_, lean_box(0), lean_box(0), v___x_2291_, v___f_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_docComment_2298_, lean_object* v_toBind_2299_, lean_object* v___f_2300_, lean_object* v_____r_2301_){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = l_Lean_validateDocComment___redArg(v_inst_2293_, v_inst_2294_, v_inst_2295_, v_inst_2296_, v_inst_2297_, v_docComment_2298_);
v___x_2303_ = lean_apply_4(v_toBind_2299_, lean_box(0), lean_box(0), v___x_2302_, v___f_2300_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_docComment_2309_, lean_object* v_toBind_2310_, lean_object* v___f_2311_, lean_object* v_____r_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2304_, v_inst_2305_, v_inst_2306_, v_inst_2307_, v_inst_2308_, v_docComment_2309_, v_toBind_2310_, v___f_2311_, v_____r_2312_);
lean_dec(v_docComment_2309_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2314_, lean_object* v_____r_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_apply_1(v___f_2314_, v_____r_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2323_, lean_object* v_declName_2324_, uint8_t v___x_2325_, lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_toBind_2328_, lean_object* v___f_2329_, lean_object* v_____do__lift_2330_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2330_, v_declName_2324_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec(v___f_2329_);
lean_dec(v_toBind_2328_);
lean_dec_ref(v_inst_2327_);
lean_dec_ref(v_inst_2326_);
lean_dec(v_declName_2324_);
goto v___jp_2331_;
}
else
{
lean_dec_ref(v___x_2334_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v___f_2323_);
v___x_2335_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2336_ = l_Lean_MessageData_ofConstName(v_declName_2324_, v___x_2325_);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_throwError___redArg(v_inst_2326_, v_inst_2327_, v___x_2339_);
v___x_2341_ = lean_apply_4(v_toBind_2328_, lean_box(0), lean_box(0), v___x_2340_, v___f_2329_);
return v___x_2341_;
}
else
{
lean_dec(v___f_2329_);
lean_dec(v_toBind_2328_);
lean_dec_ref(v_inst_2327_);
lean_dec_ref(v_inst_2326_);
lean_dec(v_declName_2324_);
goto v___jp_2331_;
}
}
v___jp_2331_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_apply_1(v___f_2323_, v___x_2332_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2342_, lean_object* v_declName_2343_, lean_object* v___x_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_, lean_object* v_toBind_2347_, lean_object* v___f_2348_, lean_object* v_____do__lift_2349_){
_start:
{
uint8_t v___x_389__boxed_2350_; lean_object* v_res_2351_; 
v___x_389__boxed_2350_ = lean_unbox(v___x_2344_);
v_res_2351_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2342_, v_declName_2343_, v___x_389__boxed_2350_, v_inst_2345_, v_inst_2346_, v_toBind_2347_, v___f_2348_, v_____do__lift_2349_);
lean_dec_ref(v_____do__lift_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_declName_2359_, lean_object* v_docComment_2360_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = l_Lean_Name_isAnonymous(v_declName_2359_);
if (v___x_2361_ == 0)
{
lean_object* v_toBind_2362_; lean_object* v_getEnv_2363_; lean_object* v_modifyEnv_2364_; lean_object* v___f_2365_; lean_object* v___f_2366_; lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; 
v_toBind_2362_ = lean_ctor_get(v_inst_2352_, 1);
lean_inc(v_toBind_2362_);
v_getEnv_2363_ = lean_ctor_get(v_inst_2355_, 0);
lean_inc(v_getEnv_2363_);
v_modifyEnv_2364_ = lean_ctor_get(v_inst_2355_, 1);
lean_inc(v_modifyEnv_2364_);
lean_dec_ref(v_inst_2355_);
lean_inc(v_declName_2359_);
v___f_2365_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2365_, 0, v_declName_2359_);
lean_closure_set(v___f_2365_, 1, v_modifyEnv_2364_);
lean_inc(v_toBind_2362_);
lean_inc(v_docComment_2360_);
lean_inc_ref(v_inst_2356_);
lean_inc_ref(v_inst_2352_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2366_, 0, v_inst_2352_);
lean_closure_set(v___f_2366_, 1, v_inst_2356_);
lean_closure_set(v___f_2366_, 2, v_docComment_2360_);
lean_closure_set(v___f_2366_, 3, v_toBind_2362_);
lean_closure_set(v___f_2366_, 4, v___f_2365_);
lean_inc(v_toBind_2362_);
lean_inc_ref(v_inst_2352_);
v___f_2367_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2367_, 0, v_inst_2352_);
lean_closure_set(v___f_2367_, 1, v_inst_2353_);
lean_closure_set(v___f_2367_, 2, v_inst_2357_);
lean_closure_set(v___f_2367_, 3, v_inst_2358_);
lean_closure_set(v___f_2367_, 4, v_inst_2354_);
lean_closure_set(v___f_2367_, 5, v_docComment_2360_);
lean_closure_set(v___f_2367_, 6, v_toBind_2362_);
lean_closure_set(v___f_2367_, 7, v___f_2366_);
lean_inc_ref(v___f_2367_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2368_, 0, v___f_2367_);
v___x_2369_ = lean_box(v___x_2361_);
lean_inc(v_toBind_2362_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2370_, 0, v___f_2367_);
lean_closure_set(v___f_2370_, 1, v_declName_2359_);
lean_closure_set(v___f_2370_, 2, v___x_2369_);
lean_closure_set(v___f_2370_, 3, v_inst_2352_);
lean_closure_set(v___f_2370_, 4, v_inst_2356_);
lean_closure_set(v___f_2370_, 5, v_toBind_2362_);
lean_closure_set(v___f_2370_, 6, v___f_2368_);
v___x_2371_ = lean_apply_4(v_toBind_2362_, lean_box(0), lean_box(0), v_getEnv_2363_, v___f_2370_);
return v___x_2371_;
}
else
{
lean_object* v_toApplicative_2372_; lean_object* v_toPure_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec(v_docComment_2360_);
lean_dec(v_declName_2359_);
lean_dec(v_inst_2358_);
lean_dec_ref(v_inst_2357_);
lean_dec_ref(v_inst_2356_);
lean_dec_ref(v_inst_2355_);
lean_dec(v_inst_2354_);
lean_dec(v_inst_2353_);
v_toApplicative_2372_ = lean_ctor_get(v_inst_2352_, 0);
lean_inc_ref(v_toApplicative_2372_);
lean_dec_ref(v_inst_2352_);
v_toPure_2373_ = lean_ctor_get(v_toApplicative_2372_, 1);
lean_inc(v_toPure_2373_);
lean_dec_ref(v_toApplicative_2372_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_apply_2(v_toPure_2373_, lean_box(0), v___x_2374_);
return v___x_2375_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_declName_2384_, lean_object* v_docComment_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_addMarkdownDocString___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_inst_2382_, v_inst_2383_, v_declName_2384_, v_docComment_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2387_, lean_object* v_docs_2388_, lean_object* v_env_2389_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = l_Lean_versoDocStringExt;
v___x_2391_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2390_, v_env_2389_, v_declName_2387_, v_docs_2388_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_2392_, lean_object* v___f_2393_, lean_object* v_____r_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_apply_1(v_modifyEnv_2392_, v___f_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_2398_, lean_object* v_modifyEnv_2399_, lean_object* v___f_2400_, uint8_t v___x_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_toBind_2404_, lean_object* v___f_2405_, lean_object* v_____do__lift_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2406_, v_declName_2398_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
lean_dec(v___f_2405_);
lean_dec(v_toBind_2404_);
lean_dec_ref(v_inst_2403_);
lean_dec_ref(v_inst_2402_);
lean_dec(v_declName_2398_);
v___x_2408_ = lean_apply_1(v_modifyEnv_2399_, v___f_2400_);
return v___x_2408_;
}
else
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2425_; 
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2425_ == 0)
{
lean_object* v_unused_2426_; 
v_unused_2426_ = lean_ctor_get(v___x_2407_, 0);
lean_dec(v_unused_2426_);
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2425_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2425_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
if (v___x_2401_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_dec_ref(v___f_2400_);
lean_dec(v_modifyEnv_2399_);
v___x_2412_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2413_ = 1;
v___x_2414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2398_, v___x_2413_);
v___x_2415_ = lean_string_append(v___x_2412_, v___x_2414_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2417_ = lean_string_append(v___x_2415_, v___x_2416_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set_tag(v___x_2410_, 3);
lean_ctor_set(v___x_2410_, 0, v___x_2417_);
v___x_2419_ = v___x_2410_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = l_Lean_MessageData_ofFormat(v___x_2419_);
v___x_2421_ = l_Lean_throwError___redArg(v_inst_2402_, v_inst_2403_, v___x_2420_);
v___x_2422_ = lean_apply_4(v_toBind_2404_, lean_box(0), lean_box(0), v___x_2421_, v___f_2405_);
return v___x_2422_;
}
}
else
{
lean_object* v___x_2424_; 
lean_del_object(v___x_2410_);
lean_dec(v___f_2405_);
lean_dec(v_toBind_2404_);
lean_dec_ref(v_inst_2403_);
lean_dec_ref(v_inst_2402_);
lean_dec(v_declName_2398_);
v___x_2424_ = lean_apply_1(v_modifyEnv_2399_, v___f_2400_);
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_2427_, lean_object* v_modifyEnv_2428_, lean_object* v___f_2429_, lean_object* v___x_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_toBind_2433_, lean_object* v___f_2434_, lean_object* v_____do__lift_2435_){
_start:
{
uint8_t v___x_303__boxed_2436_; lean_object* v_res_2437_; 
v___x_303__boxed_2436_ = lean_unbox(v___x_2430_);
v_res_2437_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_2427_, v_modifyEnv_2428_, v___f_2429_, v___x_303__boxed_2436_, v_inst_2431_, v_inst_2432_, v_toBind_2433_, v___f_2434_, v_____do__lift_2435_);
lean_dec_ref(v_____do__lift_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_declName_2441_, lean_object* v_docs_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = l_Lean_Name_isAnonymous(v_declName_2441_);
if (v___x_2443_ == 0)
{
lean_object* v_toBind_2444_; lean_object* v_getEnv_2445_; lean_object* v_modifyEnv_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; lean_object* v___x_2449_; lean_object* v___f_2450_; lean_object* v___x_2451_; 
v_toBind_2444_ = lean_ctor_get(v_inst_2438_, 1);
lean_inc(v_toBind_2444_);
v_getEnv_2445_ = lean_ctor_get(v_inst_2439_, 0);
lean_inc(v_getEnv_2445_);
v_modifyEnv_2446_ = lean_ctor_get(v_inst_2439_, 1);
lean_inc(v_modifyEnv_2446_);
lean_dec_ref(v_inst_2439_);
lean_inc(v_declName_2441_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2447_, 0, v_declName_2441_);
lean_closure_set(v___f_2447_, 1, v_docs_2442_);
lean_inc_ref(v___f_2447_);
lean_inc(v_modifyEnv_2446_);
v___f_2448_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2448_, 0, v_modifyEnv_2446_);
lean_closure_set(v___f_2448_, 1, v___f_2447_);
v___x_2449_ = lean_box(v___x_2443_);
lean_inc(v_toBind_2444_);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2450_, 0, v_declName_2441_);
lean_closure_set(v___f_2450_, 1, v_modifyEnv_2446_);
lean_closure_set(v___f_2450_, 2, v___f_2447_);
lean_closure_set(v___f_2450_, 3, v___x_2449_);
lean_closure_set(v___f_2450_, 4, v_inst_2438_);
lean_closure_set(v___f_2450_, 5, v_inst_2440_);
lean_closure_set(v___f_2450_, 6, v_toBind_2444_);
lean_closure_set(v___f_2450_, 7, v___f_2448_);
v___x_2451_ = lean_apply_4(v_toBind_2444_, lean_box(0), lean_box(0), v_getEnv_2445_, v___f_2450_);
return v___x_2451_;
}
else
{
lean_object* v_toApplicative_2452_; lean_object* v_toPure_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec_ref(v_docs_2442_);
lean_dec(v_declName_2441_);
lean_dec_ref(v_inst_2440_);
lean_dec_ref(v_inst_2439_);
v_toApplicative_2452_ = lean_ctor_get(v_inst_2438_, 0);
lean_inc_ref(v_toApplicative_2452_);
lean_dec_ref(v_inst_2438_);
v_toPure_2453_ = lean_ctor_get(v_toApplicative_2452_, 1);
lean_inc(v_toPure_2453_);
lean_dec_ref(v_toApplicative_2452_);
v___x_2454_ = lean_box(0);
v___x_2455_ = lean_apply_2(v_toPure_2453_, lean_box(0), v___x_2454_);
return v___x_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_declName_2461_, lean_object* v_docs_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2457_, v_inst_2458_, v_inst_2460_, v_declName_2461_, v_docs_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_declName_2469_, lean_object* v_docs_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_addVersoDocStringCore(v_m_2464_, v_inst_2465_, v_inst_2466_, v_inst_2467_, v_inst_2468_, v_declName_2469_, v_docs_2470_);
lean_dec(v_inst_2467_);
return v_res_2471_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_2475_, lean_object* v_inst_2476_, lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_____do__lift_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2479_, v_docs_2475_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_dec_ref(v_inst_2478_);
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_2483_ = l_Lean_stringToMessageData(v_a_2481_);
v___x_2484_ = l_Lean_indentD(v___x_2483_);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2482_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l_Lean_throwError___redArg(v_inst_2476_, v_inst_2477_, v___x_2485_);
return v___x_2486_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2488_; 
lean_dec_ref(v_inst_2477_);
lean_dec_ref(v_inst_2476_);
v_a_2487_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2480_);
v___x_2488_ = l_Lean_setEnv___redArg(v_inst_2478_, v_a_2487_);
return v___x_2488_;
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2491_ = l_Lean_stringToMessageData(v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_toBind_2494_, lean_object* v_getEnv_2495_, lean_object* v___f_2496_, lean_object* v_____do__lift_2497_){
_start:
{
lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2498_ = l_Lean_getMainModuleDoc(v_____do__lift_2497_);
v___x_2499_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2498_);
lean_dec_ref(v___x_2498_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v___f_2496_);
lean_dec(v_getEnv_2495_);
lean_dec(v_toBind_2494_);
v___x_2500_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2501_ = l_Lean_throwError___redArg(v_inst_2492_, v_inst_2493_, v___x_2500_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; 
lean_dec_ref(v_inst_2493_);
lean_dec_ref(v_inst_2492_);
v___x_2502_ = lean_apply_4(v_toBind_2494_, lean_box(0), lean_box(0), v_getEnv_2495_, v___f_2496_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_docs_2506_){
_start:
{
lean_object* v_toBind_2507_; lean_object* v_getEnv_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; 
v_toBind_2507_ = lean_ctor_get(v_inst_2503_, 1);
lean_inc(v_toBind_2507_);
v_getEnv_2508_ = lean_ctor_get(v_inst_2504_, 0);
lean_inc(v_getEnv_2508_);
lean_inc_ref(v_inst_2505_);
lean_inc_ref(v_inst_2503_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2509_, 0, v_docs_2506_);
lean_closure_set(v___f_2509_, 1, v_inst_2503_);
lean_closure_set(v___f_2509_, 2, v_inst_2505_);
lean_closure_set(v___f_2509_, 3, v_inst_2504_);
lean_inc(v_getEnv_2508_);
lean_inc(v_toBind_2507_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2510_, 0, v_inst_2503_);
lean_closure_set(v___f_2510_, 1, v_inst_2505_);
lean_closure_set(v___f_2510_, 2, v_toBind_2507_);
lean_closure_set(v___f_2510_, 3, v_getEnv_2508_);
lean_closure_set(v___f_2510_, 4, v___f_2509_);
v___x_2511_ = lean_apply_4(v_toBind_2507_, lean_box(0), lean_box(0), v_getEnv_2508_, v___f_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_docs_2517_){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2513_, v_inst_2514_, v_inst_2516_, v_docs_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_docs_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_addVersoModDocStringCore(v_m_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_, v_inst_2523_, v_docs_2524_);
lean_dec(v_inst_2522_);
return v_res_2525_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2526_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2532_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
lean_ctor_set(v___x_2532_, 2, v___x_2531_);
lean_ctor_set(v___x_2532_, 3, v___x_2531_);
lean_ctor_set(v___x_2532_, 4, v___x_2531_);
lean_ctor_set(v___x_2532_, 5, v___x_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2533_, lean_object* v_docs_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_Name_isAnonymous(v_declName_2533_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v_env_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_st_ref_get(v___y_2540_);
v_env_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc_ref(v_env_2585_);
lean_dec(v___x_2584_);
v___x_2586_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2585_, v_declName_2533_);
lean_dec_ref(v_env_2585_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_dec_ref(v___y_2535_);
v___y_2543_ = v___y_2538_;
v___y_2544_ = v___y_2540_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2601_; 
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v___x_2586_, 0);
lean_dec(v_unused_2602_);
v___x_2588_ = v___x_2586_;
v_isShared_2589_ = v_isSharedCheck_2601_;
goto v_resetjp_2587_;
}
else
{
lean_dec(v___x_2586_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2601_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
if (v___x_2583_ == 0)
{
lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec_ref(v_docs_2534_);
v___x_2590_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2591_ = 1;
v___x_2592_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2533_, v___x_2591_);
v___x_2593_ = lean_string_append(v___x_2590_, v___x_2592_);
lean_dec_ref(v___x_2592_);
v___x_2594_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2595_ = lean_string_append(v___x_2593_, v___x_2594_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 3);
lean_ctor_set(v___x_2588_, 0, v___x_2595_);
v___x_2597_ = v___x_2588_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = l_Lean_MessageData_ofFormat(v___x_2597_);
v___x_2599_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2598_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2599_;
}
}
else
{
lean_del_object(v___x_2588_);
lean_dec_ref(v___y_2535_);
v___y_2543_ = v___y_2538_;
v___y_2544_ = v___y_2540_;
goto v___jp_2542_;
}
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_docs_2534_);
lean_dec(v_declName_2533_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
v___jp_2542_:
{
lean_object* v___x_2545_; lean_object* v_env_2546_; lean_object* v_nextMacroScope_2547_; lean_object* v_ngen_2548_; lean_object* v_auxDeclNGen_2549_; lean_object* v_traceState_2550_; lean_object* v_messages_2551_; lean_object* v_infoState_2552_; lean_object* v_snapshotTasks_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2581_; 
v___x_2545_ = lean_st_ref_take(v___y_2544_);
v_env_2546_ = lean_ctor_get(v___x_2545_, 0);
v_nextMacroScope_2547_ = lean_ctor_get(v___x_2545_, 1);
v_ngen_2548_ = lean_ctor_get(v___x_2545_, 2);
v_auxDeclNGen_2549_ = lean_ctor_get(v___x_2545_, 3);
v_traceState_2550_ = lean_ctor_get(v___x_2545_, 4);
v_messages_2551_ = lean_ctor_get(v___x_2545_, 6);
v_infoState_2552_ = lean_ctor_get(v___x_2545_, 7);
v_snapshotTasks_2553_ = lean_ctor_get(v___x_2545_, 8);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2545_, 5);
lean_dec(v_unused_2582_);
v___x_2555_ = v___x_2545_;
v_isShared_2556_ = v_isSharedCheck_2581_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snapshotTasks_2553_);
lean_inc(v_infoState_2552_);
lean_inc(v_messages_2551_);
lean_inc(v_traceState_2550_);
lean_inc(v_auxDeclNGen_2549_);
lean_inc(v_ngen_2548_);
lean_inc(v_nextMacroScope_2547_);
lean_inc(v_env_2546_);
lean_dec(v___x_2545_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2581_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2557_ = l_Lean_versoDocStringExt;
v___x_2558_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2557_, v_env_2546_, v_declName_2533_, v_docs_2534_);
v___x_2559_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 5, v___x_2559_);
lean_ctor_set(v___x_2555_, 0, v___x_2558_);
v___x_2561_ = v___x_2555_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2558_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_nextMacroScope_2547_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_ngen_2548_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_auxDeclNGen_2549_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_traceState_2550_);
lean_ctor_set(v_reuseFailAlloc_2580_, 5, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2580_, 6, v_messages_2551_);
lean_ctor_set(v_reuseFailAlloc_2580_, 7, v_infoState_2552_);
lean_ctor_set(v_reuseFailAlloc_2580_, 8, v_snapshotTasks_2553_);
v___x_2561_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_mctx_2564_; lean_object* v_zetaDeltaFVarIds_2565_; lean_object* v_postponed_2566_; lean_object* v_diag_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2578_; 
v___x_2562_ = lean_st_ref_set(v___y_2544_, v___x_2561_);
v___x_2563_ = lean_st_ref_take(v___y_2543_);
v_mctx_2564_ = lean_ctor_get(v___x_2563_, 0);
v_zetaDeltaFVarIds_2565_ = lean_ctor_get(v___x_2563_, 2);
v_postponed_2566_ = lean_ctor_get(v___x_2563_, 3);
v_diag_2567_ = lean_ctor_get(v___x_2563_, 4);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2578_ == 0)
{
lean_object* v_unused_2579_; 
v_unused_2579_ = lean_ctor_get(v___x_2563_, 1);
lean_dec(v_unused_2579_);
v___x_2569_ = v___x_2563_;
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_diag_2567_);
lean_inc(v_postponed_2566_);
lean_inc(v_zetaDeltaFVarIds_2565_);
lean_inc(v_mctx_2564_);
lean_dec(v___x_2563_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2578_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2571_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 1, v___x_2571_);
v___x_2573_ = v___x_2569_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_mctx_2564_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_zetaDeltaFVarIds_2565_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_postponed_2566_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_diag_2567_);
v___x_2573_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_st_ref_set(v___y_2543_, v___x_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2605_, lean_object* v_docs_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2605_, v_docs_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2615_, lean_object* v_binders_2616_, lean_object* v_docComment_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___x_2652_; lean_object* v_env_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_st_ref_get(v_a_2623_);
v_env_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc_ref(v_env_2653_);
lean_dec(v___x_2652_);
v___x_2654_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2653_, v_declName_2615_);
lean_dec_ref(v_env_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
v___y_2626_ = v_a_2618_;
v___y_2627_ = v_a_2619_;
v___y_2628_ = v_a_2620_;
v___y_2629_ = v_a_2621_;
v___y_2630_ = v_a_2622_;
v___y_2631_ = v_a_2623_;
goto v___jp_2625_;
}
else
{
lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_docComment_2617_);
lean_dec(v_binders_2616_);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2670_);
v___x_2656_ = v___x_2654_;
v_isShared_2657_ = v_isSharedCheck_2669_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v___x_2654_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2669_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2658_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2659_ = 1;
v___x_2660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2615_, v___x_2659_);
v___x_2661_ = lean_string_append(v___x_2658_, v___x_2660_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2663_ = lean_string_append(v___x_2661_, v___x_2662_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 3);
lean_ctor_set(v___x_2656_, 0, v___x_2663_);
v___x_2665_ = v___x_2656_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = l_Lean_MessageData_ofFormat(v___x_2665_);
v___x_2667_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2666_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
return v___x_2667_;
}
}
}
v___jp_2625_:
{
lean_object* v___x_2632_; 
lean_inc(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc_ref(v___y_2628_);
lean_inc(v___y_2627_);
lean_inc_ref(v___y_2626_);
lean_inc(v_declName_2615_);
v___x_2632_ = l_Lean_versoDocString(v_declName_2615_, v_binders_2616_, v_docComment_2617_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2643_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
v_fst_2634_ = lean_ctor_get(v_a_2633_, 0);
v_snd_2635_ = lean_ctor_get(v_a_2633_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_a_2633_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2637_ = v_a_2633_;
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_dec(v_a_2633_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2643_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_fst_2634_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_snd_2635_);
v___x_2640_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2615_, v___x_2640_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v_declName_2615_);
v_a_2644_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2632_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2632_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2671_, lean_object* v_binders_2672_, lean_object* v_docComment_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_addVersoDocString(v_declName_2671_, v_binders_2672_, v_docComment_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2682_, lean_object* v_docComment_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___y_2692_; lean_object* v___y_2693_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v___x_2718_; lean_object* v_env_2719_; lean_object* v___x_2720_; 
v___x_2718_ = lean_st_ref_get(v_a_2689_);
v_env_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_env_2719_);
lean_dec(v___x_2718_);
v___x_2720_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2719_, v_declName_2682_);
lean_dec_ref(v_env_2719_);
if (lean_obj_tag(v___x_2720_) == 0)
{
v___y_2692_ = v_a_2684_;
v___y_2693_ = v_a_2685_;
v___y_2694_ = v_a_2686_;
v___y_2695_ = v_a_2687_;
v___y_2696_ = v_a_2688_;
v___y_2697_ = v_a_2689_;
goto v___jp_2691_;
}
else
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v_docComment_2683_);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v___x_2720_, 0);
lean_dec(v_unused_2736_);
v___x_2722_ = v___x_2720_;
v_isShared_2723_ = v_isSharedCheck_2735_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v___x_2720_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2735_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2724_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2682_, v___x_2725_);
v___x_2727_ = lean_string_append(v___x_2724_, v___x_2726_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2729_ = lean_string_append(v___x_2727_, v___x_2728_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 3);
lean_ctor_set(v___x_2722_, 0, v___x_2729_);
v___x_2731_ = v___x_2722_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = l_Lean_MessageData_ofFormat(v___x_2731_);
v___x_2733_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2732_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
return v___x_2733_;
}
}
}
v___jp_2691_:
{
lean_object* v___x_2698_; 
lean_inc(v___y_2697_);
lean_inc_ref(v___y_2696_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v_declName_2682_);
v___x_2698_ = l_Lean_versoDocStringFromString(v_declName_2682_, v_docComment_2683_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v_fst_2700_; lean_object* v_snd_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2709_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2698_);
v_fst_2700_ = lean_ctor_get(v_a_2699_, 0);
v_snd_2701_ = lean_ctor_get(v_a_2699_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_a_2699_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2703_ = v_a_2699_;
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_snd_2701_);
lean_inc(v_fst_2700_);
lean_dec(v_a_2699_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_fst_2700_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_snd_2701_);
v___x_2706_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2682_, v___x_2706_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
return v___x_2707_;
}
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_declName_2682_);
v_a_2710_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2698_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2698_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2737_, lean_object* v_docComment_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_addVersoDocStringFromString(v_declName_2737_, v_docComment_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2747_, lean_object* v_msgData_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
uint8_t v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = 2;
v___x_2755_ = 0;
v___x_2756_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2747_, v_msgData_2748_, v___x_2754_, v___x_2755_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2757_, lean_object* v_msgData_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2757_, v_msgData_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_ref_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2765_, lean_object* v_str_2766_, lean_object* v_as_2767_, size_t v_sz_2768_, size_t v_i_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_a_2779_; uint8_t v___x_2783_; 
v___x_2783_ = lean_usize_dec_lt(v_i_2769_, v_sz_2768_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v___y_2775_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_b_2770_);
return v___x_2784_;
}
else
{
lean_object* v_a_2785_; lean_object* v_fst_2786_; lean_object* v_snd_2787_; lean_object* v_start_2788_; lean_object* v_stop_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2809_; 
v_a_2785_ = lean_array_uget_borrowed(v_as_2767_, v_i_2769_);
v_fst_2786_ = lean_ctor_get(v_a_2785_, 0);
lean_inc(v_fst_2786_);
v_snd_2787_ = lean_ctor_get(v_a_2785_, 1);
v_start_2788_ = lean_ctor_get(v_fst_2786_, 0);
v_stop_2789_ = lean_ctor_get(v_fst_2786_, 1);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_fst_2786_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2791_ = v_fst_2786_;
v_isShared_2792_ = v_isSharedCheck_2809_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_stop_2789_);
lean_inc(v_start_2788_);
lean_dec(v_fst_2786_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2809_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_box(0);
if (lean_obj_tag(v___y_2765_) == 1)
{
lean_object* v_val_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v_val_2794_ = lean_ctor_get(v___y_2765_, 0);
v___x_2795_ = lean_nat_add(v_val_2794_, v_start_2788_);
v___x_2796_ = lean_nat_add(v_val_2794_, v_stop_2789_);
v___x_2797_ = 0;
v___x_2798_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2798_, 0, v___x_2795_);
lean_ctor_set(v___x_2798_, 1, v___x_2796_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2, v___x_2797_);
v___x_2799_ = lean_string_utf8_extract(v_str_2766_, v_start_2788_, v_stop_2789_);
lean_dec(v_stop_2789_);
lean_dec(v_start_2788_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 2);
lean_ctor_set(v___x_2791_, 1, v___x_2799_);
lean_ctor_set(v___x_2791_, 0, v___x_2798_);
v___x_2801_ = v___x_2791_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_inc(v_snd_2787_);
v___x_2802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_snd_2787_);
v___x_2803_ = l_Lean_MessageData_ofFormat(v___x_2802_);
lean_inc_ref(v___y_2775_);
v___x_2804_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2801_, v___x_2803_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec_ref(v___x_2801_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_dec_ref(v___x_2804_);
v_a_2779_ = v___x_2793_;
goto v___jp_2778_;
}
else
{
lean_dec_ref(v___y_2775_);
return v___x_2804_;
}
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
lean_del_object(v___x_2791_);
lean_dec(v_stop_2789_);
lean_dec(v_start_2788_);
lean_inc(v_snd_2787_);
v___x_2806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2806_, 0, v_snd_2787_);
v___x_2807_ = l_Lean_MessageData_ofFormat(v___x_2806_);
lean_inc_ref(v___y_2775_);
v___x_2808_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2807_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_dec_ref(v___x_2808_);
v_a_2779_ = v___x_2793_;
goto v___jp_2778_;
}
else
{
lean_dec_ref(v___y_2775_);
return v___x_2808_;
}
}
}
}
v___jp_2778_:
{
size_t v___x_2780_; size_t v___x_2781_; 
v___x_2780_ = ((size_t)1ULL);
v___x_2781_ = lean_usize_add(v_i_2769_, v___x_2780_);
v_i_2769_ = v___x_2781_;
v_b_2770_ = v_a_2779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2810_, lean_object* v_str_2811_, lean_object* v_as_2812_, lean_object* v_sz_2813_, lean_object* v_i_2814_, lean_object* v_b_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
size_t v_sz_boxed_2823_; size_t v_i_boxed_2824_; lean_object* v_res_2825_; 
v_sz_boxed_2823_ = lean_unbox_usize(v_sz_2813_);
lean_dec(v_sz_2813_);
v_i_boxed_2824_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_res_2825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2810_, v_str_2811_, v_as_2812_, v_sz_boxed_2823_, v_i_boxed_2824_, v_b_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_as_2812_);
lean_dec_ref(v_str_2811_);
lean_dec(v___y_2810_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_str_2834_; lean_object* v___y_2836_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_str_2834_ = l_Lean_TSyntax_getDocString(v_docstring_2826_);
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = l_Lean_Syntax_getArg(v_docstring_2826_, v___x_2851_);
v___x_2853_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2852_);
lean_dec(v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_box(0);
v___y_2836_ = v___x_2854_;
goto v___jp_2835_;
}
else
{
lean_object* v_val_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; 
v_val_2855_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_val_2855_);
lean_dec_ref(v___x_2853_);
v___x_2856_ = 0;
v___x_2857_ = l_Lean_SourceInfo_getPos_x3f(v_val_2855_, v___x_2856_);
lean_dec(v_val_2855_);
v___y_2836_ = v___x_2857_;
goto v___jp_2835_;
}
v___jp_2835_:
{
lean_object* v___x_2837_; lean_object* v_fst_2838_; lean_object* v___x_2839_; size_t v_sz_2840_; size_t v___x_2841_; lean_object* v___x_2842_; 
lean_inc_ref(v_str_2834_);
v___x_2837_ = l_Lean_rewriteManualLinksCore(v_str_2834_);
v_fst_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_fst_2838_);
lean_dec_ref(v___x_2837_);
v___x_2839_ = lean_box(0);
v_sz_2840_ = lean_array_size(v_fst_2838_);
v___x_2841_ = ((size_t)0ULL);
v___x_2842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2836_, v_str_2834_, v_fst_2838_, v_sz_2840_, v___x_2841_, v___x_2839_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v_fst_2838_);
lean_dec_ref(v_str_2834_);
lean_dec(v___y_2836_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2850_);
v___x_2844_ = v___x_2842_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v___x_2842_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2839_);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2839_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
return v___x_2842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v_docstring_2858_);
return v_res_2866_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2869_ = l_Lean_stringToMessageData(v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_val_2885_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = l_Lean_Syntax_getArg(v_stx_2870_, v___x_2892_);
switch(lean_obj_tag(v___x_2893_))
{
case 2:
{
lean_object* v_val_2894_; 
lean_dec_ref(v___y_2875_);
lean_dec_ref(v___y_2871_);
lean_dec(v_stx_2870_);
v_val_2894_ = lean_ctor_get(v___x_2893_, 1);
lean_inc_ref(v_val_2894_);
lean_dec_ref(v___x_2893_);
v_val_2885_ = v_val_2894_;
goto v___jp_2884_;
}
case 1:
{
lean_object* v_kind_2895_; 
v_kind_2895_ = lean_ctor_get(v___x_2893_, 1);
lean_inc(v_kind_2895_);
if (lean_obj_tag(v_kind_2895_) == 1)
{
lean_object* v_pre_2896_; 
v_pre_2896_ = lean_ctor_get(v_kind_2895_, 0);
lean_inc(v_pre_2896_);
if (lean_obj_tag(v_pre_2896_) == 1)
{
lean_object* v_pre_2897_; 
v_pre_2897_ = lean_ctor_get(v_pre_2896_, 0);
lean_inc(v_pre_2897_);
if (lean_obj_tag(v_pre_2897_) == 1)
{
lean_object* v_pre_2898_; 
v_pre_2898_ = lean_ctor_get(v_pre_2897_, 0);
lean_inc(v_pre_2898_);
if (lean_obj_tag(v_pre_2898_) == 1)
{
lean_object* v_pre_2899_; 
v_pre_2899_ = lean_ctor_get(v_pre_2898_, 0);
if (lean_obj_tag(v_pre_2899_) == 0)
{
lean_object* v_str_2900_; lean_object* v_str_2901_; lean_object* v_str_2902_; lean_object* v_str_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_str_2900_ = lean_ctor_get(v_kind_2895_, 1);
lean_inc_ref(v_str_2900_);
lean_dec_ref(v_kind_2895_);
v_str_2901_ = lean_ctor_get(v_pre_2896_, 1);
lean_inc_ref(v_str_2901_);
lean_dec_ref(v_pre_2896_);
v_str_2902_ = lean_ctor_get(v_pre_2897_, 1);
lean_inc_ref(v_str_2902_);
lean_dec_ref(v_pre_2897_);
v_str_2903_ = lean_ctor_get(v_pre_2898_, 1);
lean_inc_ref(v_str_2903_);
lean_dec_ref(v_pre_2898_);
v___x_2904_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2905_ = lean_string_dec_eq(v_str_2903_, v___x_2904_);
lean_dec_ref(v_str_2903_);
if (v___x_2905_ == 0)
{
lean_dec_ref(v_str_2902_);
lean_dec_ref(v_str_2901_);
lean_dec_ref(v_str_2900_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
else
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2907_ = lean_string_dec_eq(v_str_2902_, v___x_2906_);
lean_dec_ref(v_str_2902_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_str_2901_);
lean_dec_ref(v_str_2900_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
else
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2909_ = lean_string_dec_eq(v_str_2901_, v___x_2908_);
lean_dec_ref(v_str_2901_);
if (v___x_2909_ == 0)
{
lean_dec_ref(v_str_2900_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
else
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2911_ = lean_string_dec_eq(v_str_2900_, v___x_2910_);
lean_dec_ref(v_str_2900_);
if (v___x_2911_ == 0)
{
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_unsigned_to_nat(0u);
v___x_2913_ = l_Lean_Syntax_getArg(v___x_2893_, v___x_2912_);
lean_dec_ref(v___x_2893_);
if (lean_obj_tag(v___x_2913_) == 2)
{
lean_object* v_val_2914_; 
lean_dec_ref(v___y_2875_);
lean_dec_ref(v___y_2871_);
lean_dec(v_stx_2870_);
v_val_2914_ = lean_ctor_get(v___x_2913_, 1);
lean_inc_ref(v_val_2914_);
lean_dec_ref(v___x_2913_);
v_val_2885_ = v_val_2914_;
goto v___jp_2884_;
}
else
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_dec(v___x_2913_);
v___x_2915_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2870_);
v___x_2916_ = l_Lean_MessageData_ofSyntax(v_stx_2870_);
v___x_2917_ = l_Lean_indentD(v___x_2916_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2915_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2870_, v___x_2918_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v_stx_2870_);
return v___x_2919_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2898_);
lean_dec_ref(v_pre_2897_);
lean_dec_ref(v_pre_2896_);
lean_dec_ref(v_kind_2895_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
}
else
{
lean_dec(v_pre_2898_);
lean_dec_ref(v_pre_2897_);
lean_dec_ref(v_pre_2896_);
lean_dec_ref(v_kind_2895_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
}
else
{
lean_dec_ref(v_pre_2896_);
lean_dec(v_pre_2897_);
lean_dec_ref(v_kind_2895_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
}
else
{
lean_dec(v_pre_2896_);
lean_dec_ref(v_kind_2895_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
}
else
{
lean_dec(v_kind_2895_);
lean_dec_ref(v___x_2893_);
goto v___jp_2878_;
}
}
default: 
{
lean_dec(v___x_2893_);
goto v___jp_2878_;
}
}
v___jp_2878_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2879_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2870_);
v___x_2880_ = l_Lean_MessageData_ofSyntax(v_stx_2870_);
v___x_2881_ = l_Lean_indentD(v___x_2880_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2879_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2870_, v___x_2882_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v_stx_2870_);
return v___x_2883_;
}
v___jp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_string_utf8_byte_size(v_val_2885_);
v___x_2888_ = lean_unsigned_to_nat(2u);
v___x_2889_ = lean_nat_sub(v___x_2887_, v___x_2888_);
v___x_2890_ = lean_string_utf8_extract(v_val_2885_, v___x_2886_, v___x_2889_);
lean_dec(v___x_2889_);
lean_dec_ref(v_val_2885_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2929_, lean_object* v_docComment_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___x_3001_; 
v___x_3001_ = l_Lean_Name_isAnonymous(v_declName_2929_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v_env_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_st_ref_get(v___y_2936_);
v_env_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc_ref(v_env_3003_);
lean_dec(v___x_3002_);
v___x_3004_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3003_, v_declName_2929_);
lean_dec_ref(v_env_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
v___y_2939_ = v___y_2931_;
v___y_2940_ = v___y_2932_;
v___y_2941_ = v___y_2933_;
v___y_2942_ = v___y_2934_;
v___y_2943_ = v___y_2935_;
v___y_2944_ = v___y_2936_;
goto v___jp_2938_;
}
else
{
lean_dec_ref(v___x_3004_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_docComment_2930_);
v___x_3005_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3006_ = l_Lean_MessageData_ofConstName(v_declName_2929_, v___x_3001_);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3009_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec_ref(v___y_2935_);
return v___x_3010_;
}
else
{
v___y_2939_ = v___y_2931_;
v___y_2940_ = v___y_2932_;
v___y_2941_ = v___y_2933_;
v___y_2942_ = v___y_2934_;
v___y_2943_ = v___y_2935_;
v___y_2944_ = v___y_2936_;
goto v___jp_2938_;
}
}
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___y_2935_);
lean_dec_ref(v___y_2931_);
lean_dec(v_docComment_2930_);
lean_dec(v_declName_2929_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
v___jp_2938_:
{
lean_object* v___x_2945_; 
lean_inc_ref(v___y_2943_);
v___x_2945_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2930_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v___x_2946_; 
lean_dec_ref(v___x_2945_);
v___x_2946_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2930_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2992_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2992_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2992_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v_env_2952_; lean_object* v_nextMacroScope_2953_; lean_object* v_ngen_2954_; lean_object* v_auxDeclNGen_2955_; lean_object* v_traceState_2956_; lean_object* v_messages_2957_; lean_object* v_infoState_2958_; lean_object* v_snapshotTasks_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2990_; 
v___x_2951_ = lean_st_ref_take(v___y_2944_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
v_nextMacroScope_2953_ = lean_ctor_get(v___x_2951_, 1);
v_ngen_2954_ = lean_ctor_get(v___x_2951_, 2);
v_auxDeclNGen_2955_ = lean_ctor_get(v___x_2951_, 3);
v_traceState_2956_ = lean_ctor_get(v___x_2951_, 4);
v_messages_2957_ = lean_ctor_get(v___x_2951_, 6);
v_infoState_2958_ = lean_ctor_get(v___x_2951_, 7);
v_snapshotTasks_2959_ = lean_ctor_get(v___x_2951_, 8);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2951_, 5);
lean_dec(v_unused_2991_);
v___x_2961_ = v___x_2951_;
v_isShared_2962_ = v_isSharedCheck_2990_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_snapshotTasks_2959_);
lean_inc(v_infoState_2958_);
lean_inc(v_messages_2957_);
lean_inc(v_traceState_2956_);
lean_inc(v_auxDeclNGen_2955_);
lean_inc(v_ngen_2954_);
lean_inc(v_nextMacroScope_2953_);
lean_inc(v_env_2952_);
lean_dec(v___x_2951_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2990_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2963_ = l_Lean_docStringExt;
v___x_2964_ = l_String_removeLeadingSpaces(v_a_2947_);
v___x_2965_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2963_, v_env_2952_, v_declName_2929_, v___x_2964_);
v___x_2966_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 5, v___x_2966_);
lean_ctor_set(v___x_2961_, 0, v___x_2965_);
v___x_2968_ = v___x_2961_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_nextMacroScope_2953_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_ngen_2954_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_auxDeclNGen_2955_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_traceState_2956_);
lean_ctor_set(v_reuseFailAlloc_2989_, 5, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2989_, 6, v_messages_2957_);
lean_ctor_set(v_reuseFailAlloc_2989_, 7, v_infoState_2958_);
lean_ctor_set(v_reuseFailAlloc_2989_, 8, v_snapshotTasks_2959_);
v___x_2968_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_mctx_2971_; lean_object* v_zetaDeltaFVarIds_2972_; lean_object* v_postponed_2973_; lean_object* v_diag_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2987_; 
v___x_2969_ = lean_st_ref_set(v___y_2944_, v___x_2968_);
v___x_2970_ = lean_st_ref_take(v___y_2942_);
v_mctx_2971_ = lean_ctor_get(v___x_2970_, 0);
v_zetaDeltaFVarIds_2972_ = lean_ctor_get(v___x_2970_, 2);
v_postponed_2973_ = lean_ctor_get(v___x_2970_, 3);
v_diag_2974_ = lean_ctor_get(v___x_2970_, 4);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2970_, 1);
lean_dec(v_unused_2988_);
v___x_2976_ = v___x_2970_;
v_isShared_2977_ = v_isSharedCheck_2987_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_diag_2974_);
lean_inc(v_postponed_2973_);
lean_inc(v_zetaDeltaFVarIds_2972_);
lean_inc(v_mctx_2971_);
lean_dec(v___x_2970_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2987_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2978_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2978_);
v___x_2980_ = v___x_2976_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_mctx_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_zetaDeltaFVarIds_2972_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_postponed_2973_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_diag_2974_);
v___x_2980_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2981_ = lean_st_ref_set(v___y_2942_, v___x_2980_);
v___x_2982_ = lean_box(0);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2982_);
v___x_2984_ = v___x_2949_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
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
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_dec(v_declName_2929_);
v_a_2993_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2946_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2946_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
else
{
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2939_);
lean_dec(v_docComment_2930_);
lean_dec(v_declName_2929_);
return v___x_2945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3013_, lean_object* v_docComment_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3013_, v_docComment_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3023_, lean_object* v_declName_3024_, lean_object* v_binders_3025_, lean_object* v_docComment_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
if (v_isVerso_3023_ == 0)
{
lean_object* v___x_3034_; 
lean_dec(v_binders_3025_);
v___x_3034_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3024_, v_docComment_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3032_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
return v___x_3034_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_addVersoDocString(v_declName_3024_, v_binders_3025_, v_docComment_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3036_, lean_object* v_declName_3037_, lean_object* v_binders_3038_, lean_object* v_docComment_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
uint8_t v_isVerso_boxed_3047_; lean_object* v_res_3048_; 
v_isVerso_boxed_3047_ = lean_unbox(v_isVerso_3036_);
v_res_3048_ = l_Lean_addDocStringOf(v_isVerso_boxed_3047_, v_declName_3037_, v_binders_3038_, v_docComment_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3049_, lean_object* v_msgData_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3049_, v_msgData_3050_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3059_, lean_object* v_msgData_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3059_, v_msgData_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v_ref_3059_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3069_, lean_object* v_t_3070_){
_start:
{
if (lean_obj_tag(v_t_3070_) == 0)
{
lean_object* v_k_3071_; lean_object* v_v_3072_; lean_object* v_l_3073_; lean_object* v_r_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3728_; 
v_k_3071_ = lean_ctor_get(v_t_3070_, 1);
v_v_3072_ = lean_ctor_get(v_t_3070_, 2);
v_l_3073_ = lean_ctor_get(v_t_3070_, 3);
v_r_3074_ = lean_ctor_get(v_t_3070_, 4);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_t_3070_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_t_3070_, 0);
lean_dec(v_unused_3729_);
v___x_3076_ = v_t_3070_;
v_isShared_3077_ = v_isSharedCheck_3728_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_r_3074_);
lean_inc(v_l_3073_);
lean_inc(v_v_3072_);
lean_inc(v_k_3071_);
lean_dec(v_t_3070_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3728_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
uint8_t v___x_3078_; 
v___x_3078_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3069_, v_k_3071_);
switch(v___x_3078_)
{
case 0:
{
lean_object* v_impl_3079_; lean_object* v___x_3080_; 
v_impl_3079_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3069_, v_l_3073_);
v___x_3080_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3079_) == 0)
{
if (lean_obj_tag(v_r_3074_) == 0)
{
lean_object* v_size_3081_; lean_object* v_size_3082_; lean_object* v_k_3083_; lean_object* v_v_3084_; lean_object* v_l_3085_; lean_object* v_r_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v_size_3081_ = lean_ctor_get(v_impl_3079_, 0);
lean_inc(v_size_3081_);
v_size_3082_ = lean_ctor_get(v_r_3074_, 0);
v_k_3083_ = lean_ctor_get(v_r_3074_, 1);
v_v_3084_ = lean_ctor_get(v_r_3074_, 2);
v_l_3085_ = lean_ctor_get(v_r_3074_, 3);
lean_inc(v_l_3085_);
v_r_3086_ = lean_ctor_get(v_r_3074_, 4);
v___x_3087_ = lean_unsigned_to_nat(3u);
v___x_3088_ = lean_nat_mul(v___x_3087_, v_size_3081_);
v___x_3089_ = lean_nat_dec_lt(v___x_3088_, v_size_3082_);
lean_dec(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
lean_dec(v_l_3085_);
v___x_3090_ = lean_nat_add(v___x_3080_, v_size_3081_);
lean_dec(v_size_3081_);
v___x_3091_ = lean_nat_add(v___x_3090_, v_size_3082_);
lean_dec(v___x_3090_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 3, v_impl_3079_);
lean_ctor_set(v___x_3076_, 0, v___x_3091_);
v___x_3093_ = v___x_3076_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_impl_3079_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_r_3074_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
else
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3158_; 
lean_inc(v_r_3086_);
lean_inc(v_v_3084_);
lean_inc(v_k_3083_);
lean_inc(v_size_3082_);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; lean_object* v_unused_3160_; lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; 
v_unused_3159_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_r_3074_, 2);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_r_3074_, 1);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3163_);
v___x_3096_ = v_r_3074_;
v_isShared_3097_ = v_isSharedCheck_3158_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v_r_3074_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3158_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_size_3098_; lean_object* v_k_3099_; lean_object* v_v_3100_; lean_object* v_l_3101_; lean_object* v_r_3102_; lean_object* v_size_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_size_3098_ = lean_ctor_get(v_l_3085_, 0);
v_k_3099_ = lean_ctor_get(v_l_3085_, 1);
v_v_3100_ = lean_ctor_get(v_l_3085_, 2);
v_l_3101_ = lean_ctor_get(v_l_3085_, 3);
v_r_3102_ = lean_ctor_get(v_l_3085_, 4);
v_size_3103_ = lean_ctor_get(v_r_3086_, 0);
v___x_3104_ = lean_unsigned_to_nat(2u);
v___x_3105_ = lean_nat_mul(v___x_3104_, v_size_3103_);
v___x_3106_ = lean_nat_dec_lt(v_size_3098_, v___x_3105_);
lean_dec(v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3134_; 
lean_inc(v_r_3102_);
lean_inc(v_l_3101_);
lean_inc(v_v_3100_);
lean_inc(v_k_3099_);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_l_3085_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; lean_object* v_unused_3139_; 
v_unused_3135_ = lean_ctor_get(v_l_3085_, 4);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_l_3085_, 3);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_l_3085_, 2);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_l_3085_, 1);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_l_3085_, 0);
lean_dec(v_unused_3139_);
v___x_3108_ = v_l_3085_;
v_isShared_3109_ = v_isSharedCheck_3134_;
goto v_resetjp_3107_;
}
else
{
lean_dec(v_l_3085_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3134_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3124_; 
v___x_3110_ = lean_nat_add(v___x_3080_, v_size_3081_);
lean_dec(v_size_3081_);
v___x_3111_ = lean_nat_add(v___x_3110_, v_size_3082_);
lean_dec(v_size_3082_);
if (lean_obj_tag(v_l_3101_) == 0)
{
lean_object* v_size_3132_; 
v_size_3132_ = lean_ctor_get(v_l_3101_, 0);
lean_inc(v_size_3132_);
v___y_3124_ = v_size_3132_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_unsigned_to_nat(0u);
v___y_3124_ = v___x_3133_;
goto v___jp_3123_;
}
v___jp_3112_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_nat_add(v___y_3113_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 4, v_r_3086_);
lean_ctor_set(v___x_3108_, 3, v_r_3102_);
lean_ctor_set(v___x_3108_, 2, v_v_3084_);
lean_ctor_set(v___x_3108_, 1, v_k_3083_);
lean_ctor_set(v___x_3108_, 0, v___x_3116_);
v___x_3118_ = v___x_3108_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_k_3083_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_v_3084_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_r_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_r_3086_);
v___x_3118_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3120_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 4, v___x_3118_);
lean_ctor_set(v___x_3096_, 3, v___y_3114_);
lean_ctor_set(v___x_3096_, 2, v_v_3100_);
lean_ctor_set(v___x_3096_, 1, v_k_3099_);
lean_ctor_set(v___x_3096_, 0, v___x_3111_);
v___x_3120_ = v___x_3096_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_k_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_v_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v___y_3114_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
v___jp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_nat_add(v___x_3110_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec(v___x_3110_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_3101_);
lean_ctor_set(v___x_3076_, 3, v_impl_3079_);
lean_ctor_set(v___x_3076_, 0, v___x_3125_);
v___x_3127_ = v___x_3076_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_impl_3079_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_l_3101_);
v___x_3127_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_nat_add(v___x_3080_, v_size_3103_);
if (lean_obj_tag(v_r_3102_) == 0)
{
lean_object* v_size_3129_; 
v_size_3129_ = lean_ctor_get(v_r_3102_, 0);
lean_inc(v_size_3129_);
v___y_3113_ = v___x_3128_;
v___y_3114_ = v___x_3127_;
v___y_3115_ = v_size_3129_;
goto v___jp_3112_;
}
else
{
lean_object* v___x_3130_; 
v___x_3130_ = lean_unsigned_to_nat(0u);
v___y_3113_ = v___x_3128_;
v___y_3114_ = v___x_3127_;
v___y_3115_ = v___x_3130_;
goto v___jp_3112_;
}
}
}
}
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_del_object(v___x_3076_);
v___x_3140_ = lean_nat_add(v___x_3080_, v_size_3081_);
lean_dec(v_size_3081_);
v___x_3141_ = lean_nat_add(v___x_3140_, v_size_3082_);
lean_dec(v_size_3082_);
v___x_3142_ = lean_nat_add(v___x_3140_, v_size_3098_);
lean_dec(v___x_3140_);
lean_inc_ref(v_impl_3079_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 4, v_l_3085_);
lean_ctor_set(v___x_3096_, 3, v_impl_3079_);
lean_ctor_set(v___x_3096_, 2, v_v_3072_);
lean_ctor_set(v___x_3096_, 1, v_k_3071_);
lean_ctor_set(v___x_3096_, 0, v___x_3142_);
v___x_3144_ = v___x_3096_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v_impl_3079_);
lean_ctor_set(v_reuseFailAlloc_3157_, 4, v_l_3085_);
v___x_3144_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
v_isSharedCheck_3151_ = !lean_is_exclusive(v_impl_3079_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; 
v_unused_3152_ = lean_ctor_get(v_impl_3079_, 4);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_impl_3079_, 3);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_impl_3079_, 2);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_impl_3079_, 1);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_impl_3079_, 0);
lean_dec(v_unused_3156_);
v___x_3146_ = v_impl_3079_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_dec(v_impl_3079_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 4, v_r_3086_);
lean_ctor_set(v___x_3146_, 3, v___x_3144_);
lean_ctor_set(v___x_3146_, 2, v_v_3084_);
lean_ctor_set(v___x_3146_, 1, v_k_3083_);
lean_ctor_set(v___x_3146_, 0, v___x_3141_);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3141_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3083_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3084_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_r_3086_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v_size_3164_ = lean_ctor_get(v_impl_3079_, 0);
lean_inc(v_size_3164_);
v___x_3165_ = lean_nat_add(v___x_3080_, v_size_3164_);
lean_dec(v_size_3164_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 3, v_impl_3079_);
lean_ctor_set(v___x_3076_, 0, v___x_3165_);
v___x_3167_ = v___x_3076_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_impl_3079_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v_r_3074_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
if (lean_obj_tag(v_r_3074_) == 0)
{
lean_object* v_l_3169_; 
v_l_3169_ = lean_ctor_get(v_r_3074_, 3);
lean_inc(v_l_3169_);
if (lean_obj_tag(v_l_3169_) == 0)
{
lean_object* v_r_3170_; 
v_r_3170_ = lean_ctor_get(v_r_3074_, 4);
lean_inc(v_r_3170_);
if (lean_obj_tag(v_r_3170_) == 0)
{
lean_object* v_size_3171_; lean_object* v_k_3172_; lean_object* v_v_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3186_; 
v_size_3171_ = lean_ctor_get(v_r_3074_, 0);
v_k_3172_ = lean_ctor_get(v_r_3074_, 1);
v_v_3173_ = lean_ctor_get(v_r_3074_, 2);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; 
v_unused_3187_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3188_);
v___x_3175_ = v_r_3074_;
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_v_3173_);
lean_inc(v_k_3172_);
lean_inc(v_size_3171_);
lean_dec(v_r_3074_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3186_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_size_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
v_size_3177_ = lean_ctor_get(v_l_3169_, 0);
v___x_3178_ = lean_nat_add(v___x_3080_, v_size_3171_);
lean_dec(v_size_3171_);
v___x_3179_ = lean_nat_add(v___x_3080_, v_size_3177_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 4, v_l_3169_);
lean_ctor_set(v___x_3175_, 3, v_impl_3079_);
lean_ctor_set(v___x_3175_, 2, v_v_3072_);
lean_ctor_set(v___x_3175_, 1, v_k_3071_);
lean_ctor_set(v___x_3175_, 0, v___x_3179_);
v___x_3181_ = v___x_3175_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_impl_3079_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_l_3169_);
v___x_3181_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_r_3170_);
lean_ctor_set(v___x_3076_, 3, v___x_3181_);
lean_ctor_set(v___x_3076_, 2, v_v_3173_);
lean_ctor_set(v___x_3076_, 1, v_k_3172_);
lean_ctor_set(v___x_3076_, 0, v___x_3178_);
v___x_3183_ = v___x_3076_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3172_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3173_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_r_3170_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_k_3189_; lean_object* v_v_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3213_; 
v_k_3189_ = lean_ctor_get(v_r_3074_, 1);
v_v_3190_ = lean_ctor_get(v_r_3074_, 2);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; lean_object* v_unused_3215_; lean_object* v_unused_3216_; 
v_unused_3214_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3214_);
v_unused_3215_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3216_);
v___x_3192_ = v_r_3074_;
v_isShared_3193_ = v_isSharedCheck_3213_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_v_3190_);
lean_inc(v_k_3189_);
lean_dec(v_r_3074_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3213_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_k_3194_; lean_object* v_v_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3209_; 
v_k_3194_ = lean_ctor_get(v_l_3169_, 1);
v_v_3195_ = lean_ctor_get(v_l_3169_, 2);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_l_3169_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; lean_object* v_unused_3211_; lean_object* v_unused_3212_; 
v_unused_3210_ = lean_ctor_get(v_l_3169_, 4);
lean_dec(v_unused_3210_);
v_unused_3211_ = lean_ctor_get(v_l_3169_, 3);
lean_dec(v_unused_3211_);
v_unused_3212_ = lean_ctor_get(v_l_3169_, 0);
lean_dec(v_unused_3212_);
v___x_3197_ = v_l_3169_;
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_v_3195_);
lean_inc(v_k_3194_);
lean_dec(v_l_3169_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_unsigned_to_nat(3u);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 4, v_r_3170_);
lean_ctor_set(v___x_3197_, 3, v_r_3170_);
lean_ctor_set(v___x_3197_, 2, v_v_3072_);
lean_ctor_set(v___x_3197_, 1, v_k_3071_);
lean_ctor_set(v___x_3197_, 0, v___x_3080_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_r_3170_);
v___x_3201_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 3, v_r_3170_);
lean_ctor_set(v___x_3192_, 0, v___x_3080_);
v___x_3203_ = v___x_3192_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_r_3170_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_r_3170_);
v___x_3203_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3203_);
lean_ctor_set(v___x_3076_, 3, v___x_3201_);
lean_ctor_set(v___x_3076_, 2, v_v_3195_);
lean_ctor_set(v___x_3076_, 1, v_k_3194_);
lean_ctor_set(v___x_3076_, 0, v___x_3199_);
v___x_3205_ = v___x_3076_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_k_3194_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_v_3195_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3217_; 
v_r_3217_ = lean_ctor_get(v_r_3074_, 4);
lean_inc(v_r_3217_);
if (lean_obj_tag(v_r_3217_) == 0)
{
lean_object* v_k_3218_; lean_object* v_v_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3230_; 
v_k_3218_ = lean_ctor_get(v_r_3074_, 1);
v_v_3219_ = lean_ctor_get(v_r_3074_, 2);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; lean_object* v_unused_3232_; lean_object* v_unused_3233_; 
v_unused_3231_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3232_);
v_unused_3233_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3233_);
v___x_3221_ = v_r_3074_;
v_isShared_3222_ = v_isSharedCheck_3230_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_v_3219_);
lean_inc(v_k_3218_);
lean_dec(v_r_3074_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3230_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_unsigned_to_nat(3u);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v_l_3169_);
lean_ctor_set(v___x_3221_, 2, v_v_3072_);
lean_ctor_set(v___x_3221_, 1, v_k_3071_);
lean_ctor_set(v___x_3221_, 0, v___x_3080_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_l_3169_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_l_3169_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3227_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_r_3217_);
lean_ctor_set(v___x_3076_, 3, v___x_3225_);
lean_ctor_set(v___x_3076_, 2, v_v_3219_);
lean_ctor_set(v___x_3076_, 1, v_k_3218_);
lean_ctor_set(v___x_3076_, 0, v___x_3223_);
v___x_3227_ = v___x_3076_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3218_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3219_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_r_3217_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_size_3234_; lean_object* v_k_3235_; lean_object* v_v_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3247_; 
v_size_3234_ = lean_ctor_get(v_r_3074_, 0);
v_k_3235_ = lean_ctor_get(v_r_3074_, 1);
v_v_3236_ = lean_ctor_get(v_r_3074_, 2);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; 
v_unused_3248_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3249_);
v___x_3238_ = v_r_3074_;
v_isShared_3239_ = v_isSharedCheck_3247_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_v_3236_);
lean_inc(v_k_3235_);
lean_inc(v_size_3234_);
lean_dec(v_r_3074_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3247_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 3, v_r_3217_);
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_size_3234_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_r_3217_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_r_3217_);
v___x_3241_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = lean_unsigned_to_nat(2u);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3241_);
lean_ctor_set(v___x_3076_, 3, v_r_3217_);
lean_ctor_set(v___x_3076_, 0, v___x_3242_);
v___x_3244_ = v___x_3076_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_r_3217_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v___x_3241_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
else
{
lean_object* v___x_3251_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 3, v_r_3074_);
lean_ctor_set(v___x_3076_, 0, v___x_3080_);
v___x_3251_ = v___x_3076_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_r_3074_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_r_3074_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3076_);
lean_dec(v_v_3072_);
lean_dec(v_k_3071_);
if (lean_obj_tag(v_l_3073_) == 0)
{
if (lean_obj_tag(v_r_3074_) == 0)
{
lean_object* v_size_3253_; lean_object* v_k_3254_; lean_object* v_v_3255_; lean_object* v_l_3256_; lean_object* v_r_3257_; lean_object* v_size_3258_; lean_object* v_k_3259_; lean_object* v_v_3260_; lean_object* v_l_3261_; lean_object* v_r_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_size_3253_ = lean_ctor_get(v_l_3073_, 0);
v_k_3254_ = lean_ctor_get(v_l_3073_, 1);
v_v_3255_ = lean_ctor_get(v_l_3073_, 2);
v_l_3256_ = lean_ctor_get(v_l_3073_, 3);
v_r_3257_ = lean_ctor_get(v_l_3073_, 4);
lean_inc(v_r_3257_);
v_size_3258_ = lean_ctor_get(v_r_3074_, 0);
v_k_3259_ = lean_ctor_get(v_r_3074_, 1);
v_v_3260_ = lean_ctor_get(v_r_3074_, 2);
v_l_3261_ = lean_ctor_get(v_r_3074_, 3);
lean_inc(v_l_3261_);
v_r_3262_ = lean_ctor_get(v_r_3074_, 4);
v___x_3263_ = lean_unsigned_to_nat(1u);
v___x_3264_ = lean_nat_dec_lt(v_size_3253_, v_size_3258_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3400_; 
lean_inc(v_l_3256_);
lean_inc(v_v_3255_);
lean_inc(v_k_3254_);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; lean_object* v_unused_3405_; 
v_unused_3401_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_l_3073_, 2);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_l_3073_, 1);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3405_);
v___x_3266_ = v_l_3073_;
v_isShared_3267_ = v_isSharedCheck_3400_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v_l_3073_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3400_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v_tree_3269_; 
v___x_3268_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3254_, v_v_3255_, v_l_3256_, v_r_3257_);
v_tree_3269_ = lean_ctor_get(v___x_3268_, 2);
lean_inc(v_tree_3269_);
if (lean_obj_tag(v_tree_3269_) == 0)
{
lean_object* v_k_3270_; lean_object* v_v_3271_; lean_object* v_size_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v_k_3270_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_k_3270_);
v_v_3271_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_v_3271_);
lean_dec_ref(v___x_3268_);
v_size_3272_ = lean_ctor_get(v_tree_3269_, 0);
v___x_3273_ = lean_unsigned_to_nat(3u);
v___x_3274_ = lean_nat_mul(v___x_3273_, v_size_3272_);
v___x_3275_ = lean_nat_dec_lt(v___x_3274_, v_size_3258_);
lean_dec(v___x_3274_);
if (v___x_3275_ == 0)
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
lean_dec(v_l_3261_);
v___x_3276_ = lean_nat_add(v___x_3263_, v_size_3272_);
v___x_3277_ = lean_nat_add(v___x_3276_, v_size_3258_);
lean_dec(v___x_3276_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_r_3074_);
lean_ctor_set(v___x_3266_, 3, v_tree_3269_);
lean_ctor_set(v___x_3266_, 2, v_v_3271_);
lean_ctor_set(v___x_3266_, 1, v_k_3270_);
lean_ctor_set(v___x_3266_, 0, v___x_3277_);
v___x_3279_ = v___x_3266_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_k_3270_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_v_3271_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_tree_3269_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_r_3074_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
else
{
lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3335_; 
lean_inc(v_r_3262_);
lean_inc(v_v_3260_);
lean_inc(v_k_3259_);
lean_inc(v_size_3258_);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; lean_object* v_unused_3340_; 
v_unused_3336_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3336_);
v_unused_3337_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_r_3074_, 2);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_r_3074_, 1);
lean_dec(v_unused_3339_);
v_unused_3340_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3340_);
v___x_3282_ = v_r_3074_;
v_isShared_3283_ = v_isSharedCheck_3335_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v_r_3074_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3335_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v_size_3284_; lean_object* v_k_3285_; lean_object* v_v_3286_; lean_object* v_l_3287_; lean_object* v_r_3288_; lean_object* v_size_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_size_3284_ = lean_ctor_get(v_l_3261_, 0);
v_k_3285_ = lean_ctor_get(v_l_3261_, 1);
v_v_3286_ = lean_ctor_get(v_l_3261_, 2);
v_l_3287_ = lean_ctor_get(v_l_3261_, 3);
v_r_3288_ = lean_ctor_get(v_l_3261_, 4);
v_size_3289_ = lean_ctor_get(v_r_3262_, 0);
v___x_3290_ = lean_unsigned_to_nat(2u);
v___x_3291_ = lean_nat_mul(v___x_3290_, v_size_3289_);
v___x_3292_ = lean_nat_dec_lt(v_size_3284_, v___x_3291_);
lean_dec(v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3320_; 
lean_inc(v_r_3288_);
lean_inc(v_l_3287_);
lean_inc(v_v_3286_);
lean_inc(v_k_3285_);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_l_3261_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3321_ = lean_ctor_get(v_l_3261_, 4);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_l_3261_, 3);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_l_3261_, 2);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_l_3261_, 1);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_l_3261_, 0);
lean_dec(v_unused_3325_);
v___x_3294_ = v_l_3261_;
v_isShared_3295_ = v_isSharedCheck_3320_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v_l_3261_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3320_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3310_; 
v___x_3296_ = lean_nat_add(v___x_3263_, v_size_3272_);
v___x_3297_ = lean_nat_add(v___x_3296_, v_size_3258_);
lean_dec(v_size_3258_);
if (lean_obj_tag(v_l_3287_) == 0)
{
lean_object* v_size_3318_; 
v_size_3318_ = lean_ctor_get(v_l_3287_, 0);
lean_inc(v_size_3318_);
v___y_3310_ = v_size_3318_;
goto v___jp_3309_;
}
else
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_unsigned_to_nat(0u);
v___y_3310_ = v___x_3319_;
goto v___jp_3309_;
}
v___jp_3298_:
{
lean_object* v___x_3302_; lean_object* v___x_3304_; 
v___x_3302_ = lean_nat_add(v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 4, v_r_3262_);
lean_ctor_set(v___x_3294_, 3, v_r_3288_);
lean_ctor_set(v___x_3294_, 2, v_v_3260_);
lean_ctor_set(v___x_3294_, 1, v_k_3259_);
lean_ctor_set(v___x_3294_, 0, v___x_3302_);
v___x_3304_ = v___x_3294_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3302_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3308_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3308_, 3, v_r_3288_);
lean_ctor_set(v_reuseFailAlloc_3308_, 4, v_r_3262_);
v___x_3304_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v___x_3306_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 4, v___x_3304_);
lean_ctor_set(v___x_3282_, 3, v___y_3299_);
lean_ctor_set(v___x_3282_, 2, v_v_3286_);
lean_ctor_set(v___x_3282_, 1, v_k_3285_);
lean_ctor_set(v___x_3282_, 0, v___x_3297_);
v___x_3306_ = v___x_3282_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_k_3285_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_v_3286_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v___y_3299_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_nat_add(v___x_3296_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec(v___x_3296_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_l_3287_);
lean_ctor_set(v___x_3266_, 3, v_tree_3269_);
lean_ctor_set(v___x_3266_, 2, v_v_3271_);
lean_ctor_set(v___x_3266_, 1, v_k_3270_);
lean_ctor_set(v___x_3266_, 0, v___x_3311_);
v___x_3313_ = v___x_3266_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3270_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3271_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_tree_3269_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_l_3287_);
v___x_3313_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_nat_add(v___x_3263_, v_size_3289_);
if (lean_obj_tag(v_r_3288_) == 0)
{
lean_object* v_size_3315_; 
v_size_3315_ = lean_ctor_get(v_r_3288_, 0);
lean_inc(v_size_3315_);
v___y_3299_ = v___x_3313_;
v___y_3300_ = v___x_3314_;
v___y_3301_ = v_size_3315_;
goto v___jp_3298_;
}
else
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_unsigned_to_nat(0u);
v___y_3299_ = v___x_3313_;
v___y_3300_ = v___x_3314_;
v___y_3301_ = v___x_3316_;
goto v___jp_3298_;
}
}
}
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3326_ = lean_nat_add(v___x_3263_, v_size_3272_);
v___x_3327_ = lean_nat_add(v___x_3326_, v_size_3258_);
lean_dec(v_size_3258_);
v___x_3328_ = lean_nat_add(v___x_3326_, v_size_3284_);
lean_dec(v___x_3326_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 4, v_l_3261_);
lean_ctor_set(v___x_3282_, 3, v_tree_3269_);
lean_ctor_set(v___x_3282_, 2, v_v_3271_);
lean_ctor_set(v___x_3282_, 1, v_k_3270_);
lean_ctor_set(v___x_3282_, 0, v___x_3328_);
v___x_3330_ = v___x_3282_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3270_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3271_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_tree_3269_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_l_3261_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_r_3262_);
lean_ctor_set(v___x_3266_, 3, v___x_3330_);
lean_ctor_set(v___x_3266_, 2, v_v_3260_);
lean_ctor_set(v___x_3266_, 1, v_k_3259_);
lean_ctor_set(v___x_3266_, 0, v___x_3327_);
v___x_3332_ = v___x_3266_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_r_3262_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3394_; 
lean_inc(v_r_3262_);
lean_inc(v_v_3260_);
lean_inc(v_k_3259_);
lean_inc(v_size_3258_);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; lean_object* v_unused_3398_; lean_object* v_unused_3399_; 
v_unused_3395_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_r_3074_, 2);
lean_dec(v_unused_3397_);
v_unused_3398_ = lean_ctor_get(v_r_3074_, 1);
lean_dec(v_unused_3398_);
v_unused_3399_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3399_);
v___x_3342_ = v_r_3074_;
v_isShared_3343_ = v_isSharedCheck_3394_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_r_3074_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3394_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
if (lean_obj_tag(v_l_3261_) == 0)
{
if (lean_obj_tag(v_r_3262_) == 0)
{
lean_object* v_k_3344_; lean_object* v_v_3345_; lean_object* v_size_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v_k_3344_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_k_3344_);
v_v_3345_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_v_3345_);
lean_dec_ref(v___x_3268_);
v_size_3346_ = lean_ctor_get(v_l_3261_, 0);
v___x_3347_ = lean_nat_add(v___x_3263_, v_size_3258_);
lean_dec(v_size_3258_);
v___x_3348_ = lean_nat_add(v___x_3263_, v_size_3346_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v_l_3261_);
lean_ctor_set(v___x_3342_, 3, v_tree_3269_);
lean_ctor_set(v___x_3342_, 2, v_v_3345_);
lean_ctor_set(v___x_3342_, 1, v_k_3344_);
lean_ctor_set(v___x_3342_, 0, v___x_3348_);
v___x_3350_ = v___x_3342_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v_tree_3269_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v_l_3261_);
v___x_3350_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_r_3262_);
lean_ctor_set(v___x_3266_, 3, v___x_3350_);
lean_ctor_set(v___x_3266_, 2, v_v_3260_);
lean_ctor_set(v___x_3266_, 1, v_k_3259_);
lean_ctor_set(v___x_3266_, 0, v___x_3347_);
v___x_3352_ = v___x_3266_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3353_, 3, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_r_3262_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
else
{
lean_object* v_k_3355_; lean_object* v_v_3356_; lean_object* v_k_3357_; lean_object* v_v_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_size_3258_);
v_k_3355_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_k_3355_);
v_v_3356_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_v_3356_);
lean_dec_ref(v___x_3268_);
v_k_3357_ = lean_ctor_get(v_l_3261_, 1);
v_v_3358_ = lean_ctor_get(v_l_3261_, 2);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_l_3261_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; lean_object* v_unused_3375_; 
v_unused_3373_ = lean_ctor_get(v_l_3261_, 4);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_l_3261_, 3);
lean_dec(v_unused_3374_);
v_unused_3375_ = lean_ctor_get(v_l_3261_, 0);
lean_dec(v_unused_3375_);
v___x_3360_ = v_l_3261_;
v_isShared_3361_ = v_isSharedCheck_3372_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_v_3358_);
lean_inc(v_k_3357_);
lean_dec(v_l_3261_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3372_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3362_ = lean_unsigned_to_nat(3u);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v_r_3262_);
lean_ctor_set(v___x_3360_, 3, v_r_3262_);
lean_ctor_set(v___x_3360_, 2, v_v_3356_);
lean_ctor_set(v___x_3360_, 1, v_k_3355_);
lean_ctor_set(v___x_3360_, 0, v___x_3263_);
v___x_3364_ = v___x_3360_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_k_3355_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_v_3356_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_r_3262_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v_r_3262_);
v___x_3364_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
lean_object* v___x_3366_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 3, v_r_3262_);
lean_ctor_set(v___x_3342_, 0, v___x_3263_);
v___x_3366_ = v___x_3342_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_r_3262_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_r_3262_);
v___x_3366_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v___x_3366_);
lean_ctor_set(v___x_3266_, 3, v___x_3364_);
lean_ctor_set(v___x_3266_, 2, v_v_3358_);
lean_ctor_set(v___x_3266_, 1, v_k_3357_);
lean_ctor_set(v___x_3266_, 0, v___x_3362_);
v___x_3368_ = v___x_3266_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3262_) == 0)
{
lean_object* v_k_3376_; lean_object* v_v_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
lean_dec(v_size_3258_);
v_k_3376_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_k_3376_);
v_v_3377_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_v_3377_);
lean_dec_ref(v___x_3268_);
v___x_3378_ = lean_unsigned_to_nat(3u);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v_l_3261_);
lean_ctor_set(v___x_3342_, 2, v_v_3377_);
lean_ctor_set(v___x_3342_, 1, v_k_3376_);
lean_ctor_set(v___x_3342_, 0, v___x_3263_);
v___x_3380_ = v___x_3342_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3384_, 1, v_k_3376_);
lean_ctor_set(v_reuseFailAlloc_3384_, 2, v_v_3377_);
lean_ctor_set(v_reuseFailAlloc_3384_, 3, v_l_3261_);
lean_ctor_set(v_reuseFailAlloc_3384_, 4, v_l_3261_);
v___x_3380_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
lean_object* v___x_3382_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_r_3262_);
lean_ctor_set(v___x_3266_, 3, v___x_3380_);
lean_ctor_set(v___x_3266_, 2, v_v_3260_);
lean_ctor_set(v___x_3266_, 1, v_k_3259_);
lean_ctor_set(v___x_3266_, 0, v___x_3378_);
v___x_3382_ = v___x_3266_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3383_, 3, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3383_, 4, v_r_3262_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_k_3385_; lean_object* v_v_3386_; lean_object* v___x_3388_; 
v_k_3385_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_k_3385_);
v_v_3386_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_v_3386_);
lean_dec_ref(v___x_3268_);
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 3, v_r_3262_);
v___x_3388_ = v___x_3342_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_size_3258_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_k_3259_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_v_3260_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_r_3262_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_r_3262_);
v___x_3388_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_unsigned_to_nat(2u);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v___x_3388_);
lean_ctor_set(v___x_3266_, 3, v_r_3262_);
lean_ctor_set(v___x_3266_, 2, v_v_3386_);
lean_ctor_set(v___x_3266_, 1, v_k_3385_);
lean_ctor_set(v___x_3266_, 0, v___x_3389_);
v___x_3391_ = v___x_3266_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3385_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_r_3262_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v___x_3388_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
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
lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3558_; 
lean_inc(v_r_3262_);
lean_inc(v_v_3260_);
lean_inc(v_k_3259_);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_r_3074_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3559_ = lean_ctor_get(v_r_3074_, 4);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_r_3074_, 3);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_r_3074_, 2);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_r_3074_, 1);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_r_3074_, 0);
lean_dec(v_unused_3563_);
v___x_3407_ = v_r_3074_;
v_isShared_3408_ = v_isSharedCheck_3558_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v_r_3074_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3558_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v_tree_3410_; 
v___x_3409_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3259_, v_v_3260_, v_l_3261_, v_r_3262_);
v_tree_3410_ = lean_ctor_get(v___x_3409_, 2);
lean_inc(v_tree_3410_);
if (lean_obj_tag(v_tree_3410_) == 0)
{
lean_object* v_k_3411_; lean_object* v_v_3412_; lean_object* v_size_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v_k_3411_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_k_3411_);
v_v_3412_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_v_3412_);
lean_dec_ref(v___x_3409_);
v_size_3413_ = lean_ctor_get(v_tree_3410_, 0);
v___x_3414_ = lean_unsigned_to_nat(3u);
v___x_3415_ = lean_nat_mul(v___x_3414_, v_size_3413_);
v___x_3416_ = lean_nat_dec_lt(v___x_3415_, v_size_3253_);
lean_dec(v___x_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3420_; 
lean_dec(v_r_3257_);
v___x_3417_ = lean_nat_add(v___x_3263_, v_size_3253_);
v___x_3418_ = lean_nat_add(v___x_3417_, v_size_3413_);
lean_dec(v___x_3417_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_tree_3410_);
lean_ctor_set(v___x_3407_, 3, v_l_3073_);
lean_ctor_set(v___x_3407_, 2, v_v_3412_);
lean_ctor_set(v___x_3407_, 1, v_k_3411_);
lean_ctor_set(v___x_3407_, 0, v___x_3418_);
v___x_3420_ = v___x_3407_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v_k_3411_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_v_3412_);
lean_ctor_set(v_reuseFailAlloc_3421_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3421_, 4, v_tree_3410_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
else
{
lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3487_; 
lean_inc(v_l_3256_);
lean_inc(v_v_3255_);
lean_inc(v_k_3254_);
lean_inc(v_size_3253_);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; lean_object* v_unused_3492_; 
v_unused_3488_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_l_3073_, 2);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_l_3073_, 1);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3492_);
v___x_3423_ = v_l_3073_;
v_isShared_3424_ = v_isSharedCheck_3487_;
goto v_resetjp_3422_;
}
else
{
lean_dec(v_l_3073_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3487_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v_size_3425_; lean_object* v_size_3426_; lean_object* v_k_3427_; lean_object* v_v_3428_; lean_object* v_l_3429_; lean_object* v_r_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v_size_3425_ = lean_ctor_get(v_l_3256_, 0);
v_size_3426_ = lean_ctor_get(v_r_3257_, 0);
v_k_3427_ = lean_ctor_get(v_r_3257_, 1);
v_v_3428_ = lean_ctor_get(v_r_3257_, 2);
v_l_3429_ = lean_ctor_get(v_r_3257_, 3);
v_r_3430_ = lean_ctor_get(v_r_3257_, 4);
v___x_3431_ = lean_unsigned_to_nat(2u);
v___x_3432_ = lean_nat_mul(v___x_3431_, v_size_3425_);
v___x_3433_ = lean_nat_dec_lt(v_size_3426_, v___x_3432_);
lean_dec(v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3471_; 
lean_inc(v_r_3430_);
lean_inc(v_l_3429_);
lean_inc(v_v_3428_);
lean_inc(v_k_3427_);
lean_del_object(v___x_3423_);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_r_3257_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; lean_object* v_unused_3474_; lean_object* v_unused_3475_; lean_object* v_unused_3476_; 
v_unused_3472_ = lean_ctor_get(v_r_3257_, 4);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_r_3257_, 3);
lean_dec(v_unused_3473_);
v_unused_3474_ = lean_ctor_get(v_r_3257_, 2);
lean_dec(v_unused_3474_);
v_unused_3475_ = lean_ctor_get(v_r_3257_, 1);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_r_3257_, 0);
lean_dec(v_unused_3476_);
v___x_3435_ = v_r_3257_;
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v_r_3257_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3471_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___x_3459_; lean_object* v___y_3461_; 
v___x_3437_ = lean_nat_add(v___x_3263_, v_size_3253_);
lean_dec(v_size_3253_);
v___x_3438_ = lean_nat_add(v___x_3437_, v_size_3413_);
lean_dec(v___x_3437_);
v___x_3459_ = lean_nat_add(v___x_3263_, v_size_3425_);
if (lean_obj_tag(v_l_3429_) == 0)
{
lean_object* v_size_3469_; 
v_size_3469_ = lean_ctor_get(v_l_3429_, 0);
lean_inc(v_size_3469_);
v___y_3461_ = v_size_3469_;
goto v___jp_3460_;
}
else
{
lean_object* v___x_3470_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v___y_3461_ = v___x_3470_;
goto v___jp_3460_;
}
v___jp_3439_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_nat_add(v___y_3440_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec(v___y_3440_);
lean_inc_ref(v_tree_3410_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 4, v_tree_3410_);
lean_ctor_set(v___x_3435_, 3, v_r_3430_);
lean_ctor_set(v___x_3435_, 2, v_v_3412_);
lean_ctor_set(v___x_3435_, 1, v_k_3411_);
lean_ctor_set(v___x_3435_, 0, v___x_3443_);
v___x_3445_ = v___x_3435_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_k_3411_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_v_3412_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_r_3430_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_tree_3410_);
v___x_3445_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_isSharedCheck_3452_ = !lean_is_exclusive(v_tree_3410_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3453_ = lean_ctor_get(v_tree_3410_, 4);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_tree_3410_, 3);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_tree_3410_, 2);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_tree_3410_, 1);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_tree_3410_, 0);
lean_dec(v_unused_3457_);
v___x_3447_ = v_tree_3410_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v_tree_3410_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 4, v___x_3445_);
lean_ctor_set(v___x_3447_, 3, v___y_3441_);
lean_ctor_set(v___x_3447_, 2, v_v_3428_);
lean_ctor_set(v___x_3447_, 1, v_k_3427_);
lean_ctor_set(v___x_3447_, 0, v___x_3438_);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v___y_3441_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v___x_3445_);
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
v___jp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_nat_add(v___x_3459_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec(v___x_3459_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_l_3429_);
lean_ctor_set(v___x_3407_, 3, v_l_3256_);
lean_ctor_set(v___x_3407_, 2, v_v_3255_);
lean_ctor_set(v___x_3407_, 1, v_k_3254_);
lean_ctor_set(v___x_3407_, 0, v___x_3462_);
v___x_3464_ = v___x_3407_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_l_3256_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_l_3429_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_nat_add(v___x_3263_, v_size_3413_);
if (lean_obj_tag(v_r_3430_) == 0)
{
lean_object* v_size_3466_; 
v_size_3466_ = lean_ctor_get(v_r_3430_, 0);
lean_inc(v_size_3466_);
v___y_3440_ = v___x_3465_;
v___y_3441_ = v___x_3464_;
v___y_3442_ = v_size_3466_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_unsigned_to_nat(0u);
v___y_3440_ = v___x_3465_;
v___y_3441_ = v___x_3464_;
v___y_3442_ = v___x_3467_;
goto v___jp_3439_;
}
}
}
}
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3477_ = lean_nat_add(v___x_3263_, v_size_3253_);
lean_dec(v_size_3253_);
v___x_3478_ = lean_nat_add(v___x_3477_, v_size_3413_);
lean_dec(v___x_3477_);
v___x_3479_ = lean_nat_add(v___x_3263_, v_size_3413_);
v___x_3480_ = lean_nat_add(v___x_3479_, v_size_3426_);
lean_dec(v___x_3479_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_tree_3410_);
lean_ctor_set(v___x_3407_, 3, v_r_3257_);
lean_ctor_set(v___x_3407_, 2, v_v_3412_);
lean_ctor_set(v___x_3407_, 1, v_k_3411_);
lean_ctor_set(v___x_3407_, 0, v___x_3480_);
v___x_3482_ = v___x_3407_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3411_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3412_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_r_3257_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_tree_3410_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 4, v___x_3482_);
lean_ctor_set(v___x_3423_, 0, v___x_3478_);
v___x_3484_ = v___x_3423_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_3256_);
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
}
}
}
else
{
if (lean_obj_tag(v_l_3256_) == 0)
{
lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3516_; 
lean_inc_ref(v_l_3256_);
lean_inc(v_v_3255_);
lean_inc(v_k_3254_);
lean_inc(v_size_3253_);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3516_ == 0)
{
lean_object* v_unused_3517_; lean_object* v_unused_3518_; lean_object* v_unused_3519_; lean_object* v_unused_3520_; lean_object* v_unused_3521_; 
v_unused_3517_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3517_);
v_unused_3518_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_l_3073_, 2);
lean_dec(v_unused_3519_);
v_unused_3520_ = lean_ctor_get(v_l_3073_, 1);
lean_dec(v_unused_3520_);
v_unused_3521_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3521_);
v___x_3494_ = v_l_3073_;
v_isShared_3495_ = v_isSharedCheck_3516_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v_l_3073_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3516_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
if (lean_obj_tag(v_r_3257_) == 0)
{
lean_object* v_k_3496_; lean_object* v_v_3497_; lean_object* v_size_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3502_; 
v_k_3496_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_k_3496_);
v_v_3497_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_v_3497_);
lean_dec_ref(v___x_3409_);
v_size_3498_ = lean_ctor_get(v_r_3257_, 0);
v___x_3499_ = lean_nat_add(v___x_3263_, v_size_3253_);
lean_dec(v_size_3253_);
v___x_3500_ = lean_nat_add(v___x_3263_, v_size_3498_);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_tree_3410_);
lean_ctor_set(v___x_3407_, 3, v_r_3257_);
lean_ctor_set(v___x_3407_, 2, v_v_3497_);
lean_ctor_set(v___x_3407_, 1, v_k_3496_);
lean_ctor_set(v___x_3407_, 0, v___x_3500_);
v___x_3502_ = v___x_3407_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_k_3496_);
lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_v_3497_);
lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_r_3257_);
lean_ctor_set(v_reuseFailAlloc_3506_, 4, v_tree_3410_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v___x_3502_);
lean_ctor_set(v___x_3494_, 0, v___x_3499_);
v___x_3504_ = v___x_3494_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_l_3256_);
lean_ctor_set(v_reuseFailAlloc_3505_, 4, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
else
{
lean_object* v_k_3507_; lean_object* v_v_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
lean_dec(v_size_3253_);
v_k_3507_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_k_3507_);
v_v_3508_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_v_3508_);
lean_dec_ref(v___x_3409_);
v___x_3509_ = lean_unsigned_to_nat(3u);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_r_3257_);
lean_ctor_set(v___x_3407_, 3, v_r_3257_);
lean_ctor_set(v___x_3407_, 2, v_v_3508_);
lean_ctor_set(v___x_3407_, 1, v_k_3507_);
lean_ctor_set(v___x_3407_, 0, v___x_3263_);
v___x_3511_ = v___x_3407_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3507_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3508_);
lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_r_3257_);
lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_r_3257_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 4, v___x_3511_);
lean_ctor_set(v___x_3494_, 0, v___x_3509_);
v___x_3513_ = v___x_3494_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3514_, 3, v_l_3256_);
lean_ctor_set(v_reuseFailAlloc_3514_, 4, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3257_) == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3546_; 
lean_inc(v_l_3256_);
lean_inc(v_v_3255_);
lean_inc(v_k_3254_);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; lean_object* v_unused_3551_; 
v_unused_3547_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_l_3073_, 2);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_l_3073_, 1);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3551_);
v___x_3523_ = v_l_3073_;
v_isShared_3524_ = v_isSharedCheck_3546_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_l_3073_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3546_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v_k_3525_; lean_object* v_v_3526_; lean_object* v_k_3527_; lean_object* v_v_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3542_; 
v_k_3525_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_k_3525_);
v_v_3526_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_v_3526_);
lean_dec_ref(v___x_3409_);
v_k_3527_ = lean_ctor_get(v_r_3257_, 1);
v_v_3528_ = lean_ctor_get(v_r_3257_, 2);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_r_3257_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; lean_object* v_unused_3544_; lean_object* v_unused_3545_; 
v_unused_3543_ = lean_ctor_get(v_r_3257_, 4);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_r_3257_, 3);
lean_dec(v_unused_3544_);
v_unused_3545_ = lean_ctor_get(v_r_3257_, 0);
lean_dec(v_unused_3545_);
v___x_3530_ = v_r_3257_;
v_isShared_3531_ = v_isSharedCheck_3542_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_v_3528_);
lean_inc(v_k_3527_);
lean_dec(v_r_3257_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3542_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_unsigned_to_nat(3u);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 4, v_l_3256_);
lean_ctor_set(v___x_3530_, 3, v_l_3256_);
lean_ctor_set(v___x_3530_, 2, v_v_3255_);
lean_ctor_set(v___x_3530_, 1, v_k_3254_);
lean_ctor_set(v___x_3530_, 0, v___x_3263_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3541_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3541_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3541_, 3, v_l_3256_);
lean_ctor_set(v_reuseFailAlloc_3541_, 4, v_l_3256_);
v___x_3534_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_l_3256_);
lean_ctor_set(v___x_3407_, 3, v_l_3256_);
lean_ctor_set(v___x_3407_, 2, v_v_3526_);
lean_ctor_set(v___x_3407_, 1, v_k_3525_);
lean_ctor_set(v___x_3407_, 0, v___x_3263_);
v___x_3536_ = v___x_3407_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3540_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3540_, 3, v_l_3256_);
lean_ctor_set(v_reuseFailAlloc_3540_, 4, v_l_3256_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v___x_3536_);
lean_ctor_set(v___x_3523_, 3, v___x_3534_);
lean_ctor_set(v___x_3523_, 2, v_v_3528_);
lean_ctor_set(v___x_3523_, 1, v_k_3527_);
lean_ctor_set(v___x_3523_, 0, v___x_3532_);
v___x_3538_ = v___x_3523_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_k_3527_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_v_3528_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
}
else
{
lean_object* v_k_3552_; lean_object* v_v_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v_k_3552_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_k_3552_);
v_v_3553_ = lean_ctor_get(v___x_3409_, 1);
lean_inc(v_v_3553_);
lean_dec_ref(v___x_3409_);
v___x_3554_ = lean_unsigned_to_nat(2u);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 4, v_r_3257_);
lean_ctor_set(v___x_3407_, 3, v_l_3073_);
lean_ctor_set(v___x_3407_, 2, v_v_3553_);
lean_ctor_set(v___x_3407_, 1, v_k_3552_);
lean_ctor_set(v___x_3407_, 0, v___x_3554_);
v___x_3556_ = v___x_3407_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3552_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_v_3553_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_r_3257_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
return v_l_3073_;
}
}
else
{
return v_r_3074_;
}
}
default: 
{
lean_object* v_impl_3564_; lean_object* v___x_3565_; 
v_impl_3564_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3069_, v_r_3074_);
v___x_3565_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3564_) == 0)
{
if (lean_obj_tag(v_l_3073_) == 0)
{
lean_object* v_size_3566_; lean_object* v_size_3567_; lean_object* v_k_3568_; lean_object* v_v_3569_; lean_object* v_l_3570_; lean_object* v_r_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; uint8_t v___x_3574_; 
v_size_3566_ = lean_ctor_get(v_impl_3564_, 0);
lean_inc(v_size_3566_);
v_size_3567_ = lean_ctor_get(v_l_3073_, 0);
v_k_3568_ = lean_ctor_get(v_l_3073_, 1);
v_v_3569_ = lean_ctor_get(v_l_3073_, 2);
v_l_3570_ = lean_ctor_get(v_l_3073_, 3);
v_r_3571_ = lean_ctor_get(v_l_3073_, 4);
lean_inc(v_r_3571_);
v___x_3572_ = lean_unsigned_to_nat(3u);
v___x_3573_ = lean_nat_mul(v___x_3572_, v_size_3566_);
v___x_3574_ = lean_nat_dec_lt(v___x_3573_, v_size_3567_);
lean_dec(v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_dec(v_r_3571_);
v___x_3575_ = lean_nat_add(v___x_3565_, v_size_3567_);
v___x_3576_ = lean_nat_add(v___x_3575_, v_size_3566_);
lean_dec(v_size_3566_);
lean_dec(v___x_3575_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_impl_3564_);
lean_ctor_set(v___x_3076_, 0, v___x_3576_);
v___x_3578_ = v___x_3076_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3579_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3579_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3579_, 4, v_impl_3564_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
else
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3645_; 
lean_inc(v_l_3570_);
lean_inc(v_v_3569_);
lean_inc(v_k_3568_);
lean_inc(v_size_3567_);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; lean_object* v_unused_3647_; lean_object* v_unused_3648_; lean_object* v_unused_3649_; lean_object* v_unused_3650_; 
v_unused_3646_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3646_);
v_unused_3647_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_l_3073_, 2);
lean_dec(v_unused_3648_);
v_unused_3649_ = lean_ctor_get(v_l_3073_, 1);
lean_dec(v_unused_3649_);
v_unused_3650_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3650_);
v___x_3581_ = v_l_3073_;
v_isShared_3582_ = v_isSharedCheck_3645_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_l_3073_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3645_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v_size_3583_; lean_object* v_size_3584_; lean_object* v_k_3585_; lean_object* v_v_3586_; lean_object* v_l_3587_; lean_object* v_r_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_size_3583_ = lean_ctor_get(v_l_3570_, 0);
v_size_3584_ = lean_ctor_get(v_r_3571_, 0);
v_k_3585_ = lean_ctor_get(v_r_3571_, 1);
v_v_3586_ = lean_ctor_get(v_r_3571_, 2);
v_l_3587_ = lean_ctor_get(v_r_3571_, 3);
v_r_3588_ = lean_ctor_get(v_r_3571_, 4);
v___x_3589_ = lean_unsigned_to_nat(2u);
v___x_3590_ = lean_nat_mul(v___x_3589_, v_size_3583_);
v___x_3591_ = lean_nat_dec_lt(v_size_3584_, v___x_3590_);
lean_dec(v___x_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3620_; 
lean_inc(v_r_3588_);
lean_inc(v_l_3587_);
lean_inc(v_v_3586_);
lean_inc(v_k_3585_);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_r_3571_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; lean_object* v_unused_3624_; lean_object* v_unused_3625_; 
v_unused_3621_ = lean_ctor_get(v_r_3571_, 4);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_r_3571_, 3);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_r_3571_, 2);
lean_dec(v_unused_3623_);
v_unused_3624_ = lean_ctor_get(v_r_3571_, 1);
lean_dec(v_unused_3624_);
v_unused_3625_ = lean_ctor_get(v_r_3571_, 0);
lean_dec(v_unused_3625_);
v___x_3593_ = v_r_3571_;
v_isShared_3594_ = v_isSharedCheck_3620_;
goto v_resetjp_3592_;
}
else
{
lean_dec(v_r_3571_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3620_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___x_3608_; lean_object* v___y_3610_; 
v___x_3595_ = lean_nat_add(v___x_3565_, v_size_3567_);
lean_dec(v_size_3567_);
v___x_3596_ = lean_nat_add(v___x_3595_, v_size_3566_);
lean_dec(v___x_3595_);
v___x_3608_ = lean_nat_add(v___x_3565_, v_size_3583_);
if (lean_obj_tag(v_l_3587_) == 0)
{
lean_object* v_size_3618_; 
v_size_3618_ = lean_ctor_get(v_l_3587_, 0);
lean_inc(v_size_3618_);
v___y_3610_ = v_size_3618_;
goto v___jp_3609_;
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
v___y_3610_ = v___x_3619_;
goto v___jp_3609_;
}
v___jp_3597_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_nat_add(v___y_3598_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec(v___y_3598_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 4, v_impl_3564_);
lean_ctor_set(v___x_3593_, 3, v_r_3588_);
lean_ctor_set(v___x_3593_, 2, v_v_3072_);
lean_ctor_set(v___x_3593_, 1, v_k_3071_);
lean_ctor_set(v___x_3593_, 0, v___x_3601_);
v___x_3603_ = v___x_3593_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_r_3588_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_impl_3564_);
v___x_3603_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v___x_3603_);
lean_ctor_set(v___x_3581_, 3, v___y_3599_);
lean_ctor_set(v___x_3581_, 2, v_v_3586_);
lean_ctor_set(v___x_3581_, 1, v_k_3585_);
lean_ctor_set(v___x_3581_, 0, v___x_3596_);
v___x_3605_ = v___x_3581_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_k_3585_);
lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_v_3586_);
lean_ctor_set(v_reuseFailAlloc_3606_, 3, v___y_3599_);
lean_ctor_set(v_reuseFailAlloc_3606_, 4, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
v___jp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_nat_add(v___x_3608_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec(v___x_3608_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_3587_);
lean_ctor_set(v___x_3076_, 3, v_l_3570_);
lean_ctor_set(v___x_3076_, 2, v_v_3569_);
lean_ctor_set(v___x_3076_, 1, v_k_3568_);
lean_ctor_set(v___x_3076_, 0, v___x_3611_);
v___x_3613_ = v___x_3076_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3568_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3569_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_l_3570_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v_l_3587_);
v___x_3613_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_nat_add(v___x_3565_, v_size_3566_);
lean_dec(v_size_3566_);
if (lean_obj_tag(v_r_3588_) == 0)
{
lean_object* v_size_3615_; 
v_size_3615_ = lean_ctor_get(v_r_3588_, 0);
lean_inc(v_size_3615_);
v___y_3598_ = v___x_3614_;
v___y_3599_ = v___x_3613_;
v___y_3600_ = v_size_3615_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_unsigned_to_nat(0u);
v___y_3598_ = v___x_3614_;
v___y_3599_ = v___x_3613_;
v___y_3600_ = v___x_3616_;
goto v___jp_3597_;
}
}
}
}
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
lean_del_object(v___x_3076_);
v___x_3626_ = lean_nat_add(v___x_3565_, v_size_3567_);
lean_dec(v_size_3567_);
v___x_3627_ = lean_nat_add(v___x_3626_, v_size_3566_);
lean_dec(v___x_3626_);
v___x_3628_ = lean_nat_add(v___x_3565_, v_size_3566_);
lean_dec(v_size_3566_);
v___x_3629_ = lean_nat_add(v___x_3628_, v_size_3584_);
lean_dec(v___x_3628_);
lean_inc_ref(v_impl_3564_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v_impl_3564_);
lean_ctor_set(v___x_3581_, 3, v_r_3571_);
lean_ctor_set(v___x_3581_, 2, v_v_3072_);
lean_ctor_set(v___x_3581_, 1, v_k_3071_);
lean_ctor_set(v___x_3581_, 0, v___x_3629_);
v___x_3631_ = v___x_3581_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_r_3571_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_impl_3564_);
v___x_3631_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
v_isSharedCheck_3638_ = !lean_is_exclusive(v_impl_3564_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; lean_object* v_unused_3640_; lean_object* v_unused_3641_; lean_object* v_unused_3642_; lean_object* v_unused_3643_; 
v_unused_3639_ = lean_ctor_get(v_impl_3564_, 4);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_impl_3564_, 3);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v_impl_3564_, 2);
lean_dec(v_unused_3641_);
v_unused_3642_ = lean_ctor_get(v_impl_3564_, 1);
lean_dec(v_unused_3642_);
v_unused_3643_ = lean_ctor_get(v_impl_3564_, 0);
lean_dec(v_unused_3643_);
v___x_3633_ = v_impl_3564_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_dec(v_impl_3564_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 4, v___x_3631_);
lean_ctor_set(v___x_3633_, 3, v_l_3570_);
lean_ctor_set(v___x_3633_, 2, v_v_3569_);
lean_ctor_set(v___x_3633_, 1, v_k_3568_);
lean_ctor_set(v___x_3633_, 0, v___x_3627_);
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3568_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3569_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_l_3570_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v___x_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v_size_3651_ = lean_ctor_get(v_impl_3564_, 0);
lean_inc(v_size_3651_);
v___x_3652_ = lean_nat_add(v___x_3565_, v_size_3651_);
lean_dec(v_size_3651_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_impl_3564_);
lean_ctor_set(v___x_3076_, 0, v___x_3652_);
v___x_3654_ = v___x_3076_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3655_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3655_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3655_, 4, v_impl_3564_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
else
{
if (lean_obj_tag(v_l_3073_) == 0)
{
lean_object* v_l_3656_; 
v_l_3656_ = lean_ctor_get(v_l_3073_, 3);
if (lean_obj_tag(v_l_3656_) == 0)
{
lean_object* v_r_3657_; 
lean_inc_ref(v_l_3656_);
v_r_3657_ = lean_ctor_get(v_l_3073_, 4);
lean_inc(v_r_3657_);
if (lean_obj_tag(v_r_3657_) == 0)
{
lean_object* v_size_3658_; lean_object* v_k_3659_; lean_object* v_v_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3673_; 
v_size_3658_ = lean_ctor_get(v_l_3073_, 0);
v_k_3659_ = lean_ctor_get(v_l_3073_, 1);
v_v_3660_ = lean_ctor_get(v_l_3073_, 2);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; lean_object* v_unused_3675_; 
v_unused_3674_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3675_);
v___x_3662_ = v_l_3073_;
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_v_3660_);
lean_inc(v_k_3659_);
lean_inc(v_size_3658_);
lean_dec(v_l_3073_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3673_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_size_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3668_; 
v_size_3664_ = lean_ctor_get(v_r_3657_, 0);
v___x_3665_ = lean_nat_add(v___x_3565_, v_size_3658_);
lean_dec(v_size_3658_);
v___x_3666_ = lean_nat_add(v___x_3565_, v_size_3664_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_impl_3564_);
lean_ctor_set(v___x_3662_, 3, v_r_3657_);
lean_ctor_set(v___x_3662_, 2, v_v_3072_);
lean_ctor_set(v___x_3662_, 1, v_k_3071_);
lean_ctor_set(v___x_3662_, 0, v___x_3666_);
v___x_3668_ = v___x_3662_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_r_3657_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v_impl_3564_);
v___x_3668_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3670_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3668_);
lean_ctor_set(v___x_3076_, 3, v_l_3656_);
lean_ctor_set(v___x_3076_, 2, v_v_3660_);
lean_ctor_set(v___x_3076_, 1, v_k_3659_);
lean_ctor_set(v___x_3076_, 0, v___x_3665_);
v___x_3670_ = v___x_3076_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_k_3659_);
lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_v_3660_);
lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3671_, 4, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
return v___x_3670_;
}
}
}
}
else
{
lean_object* v_k_3676_; lean_object* v_v_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3688_; 
v_k_3676_ = lean_ctor_get(v_l_3073_, 1);
v_v_3677_ = lean_ctor_get(v_l_3073_, 2);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; 
v_unused_3689_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3691_);
v___x_3679_ = v_l_3073_;
v_isShared_3680_ = v_isSharedCheck_3688_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_v_3677_);
lean_inc(v_k_3676_);
lean_dec(v_l_3073_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3688_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_unsigned_to_nat(3u);
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 3, v_r_3657_);
lean_ctor_set(v___x_3679_, 2, v_v_3072_);
lean_ctor_set(v___x_3679_, 1, v_k_3071_);
lean_ctor_set(v___x_3679_, 0, v___x_3565_);
v___x_3683_ = v___x_3679_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_r_3657_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_r_3657_);
v___x_3683_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3683_);
lean_ctor_set(v___x_3076_, 3, v_l_3656_);
lean_ctor_set(v___x_3076_, 2, v_v_3677_);
lean_ctor_set(v___x_3076_, 1, v_k_3676_);
lean_ctor_set(v___x_3076_, 0, v___x_3681_);
v___x_3685_ = v___x_3076_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3686_, 4, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
else
{
lean_object* v_r_3692_; 
v_r_3692_ = lean_ctor_get(v_l_3073_, 4);
lean_inc(v_r_3692_);
if (lean_obj_tag(v_r_3692_) == 0)
{
lean_object* v_k_3693_; lean_object* v_v_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3717_; 
lean_inc(v_l_3656_);
v_k_3693_ = lean_ctor_get(v_l_3073_, 1);
v_v_3694_ = lean_ctor_get(v_l_3073_, 2);
v_isSharedCheck_3717_ = !lean_is_exclusive(v_l_3073_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; 
v_unused_3718_ = lean_ctor_get(v_l_3073_, 4);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_l_3073_, 3);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_l_3073_, 0);
lean_dec(v_unused_3720_);
v___x_3696_ = v_l_3073_;
v_isShared_3697_ = v_isSharedCheck_3717_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_v_3694_);
lean_inc(v_k_3693_);
lean_dec(v_l_3073_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3717_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v_k_3698_; lean_object* v_v_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3713_; 
v_k_3698_ = lean_ctor_get(v_r_3692_, 1);
v_v_3699_ = lean_ctor_get(v_r_3692_, 2);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_r_3692_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; 
v_unused_3714_ = lean_ctor_get(v_r_3692_, 4);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_r_3692_, 3);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_r_3692_, 0);
lean_dec(v_unused_3716_);
v___x_3701_ = v_r_3692_;
v_isShared_3702_ = v_isSharedCheck_3713_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_v_3699_);
lean_inc(v_k_3698_);
lean_dec(v_r_3692_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3713_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_unsigned_to_nat(3u);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v_l_3656_);
lean_ctor_set(v___x_3701_, 3, v_l_3656_);
lean_ctor_set(v___x_3701_, 2, v_v_3694_);
lean_ctor_set(v___x_3701_, 1, v_k_3693_);
lean_ctor_set(v___x_3701_, 0, v___x_3565_);
v___x_3705_ = v___x_3701_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3712_, 1, v_k_3693_);
lean_ctor_set(v_reuseFailAlloc_3712_, 2, v_v_3694_);
lean_ctor_set(v_reuseFailAlloc_3712_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3712_, 4, v_l_3656_);
v___x_3705_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set(v___x_3696_, 4, v_l_3656_);
lean_ctor_set(v___x_3696_, 2, v_v_3072_);
lean_ctor_set(v___x_3696_, 1, v_k_3071_);
lean_ctor_set(v___x_3696_, 0, v___x_3565_);
v___x_3707_ = v___x_3696_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3711_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3711_, 3, v_l_3656_);
lean_ctor_set(v_reuseFailAlloc_3711_, 4, v_l_3656_);
v___x_3707_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3709_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v___x_3707_);
lean_ctor_set(v___x_3076_, 3, v___x_3705_);
lean_ctor_set(v___x_3076_, 2, v_v_3699_);
lean_ctor_set(v___x_3076_, 1, v_k_3698_);
lean_ctor_set(v___x_3076_, 0, v___x_3703_);
v___x_3709_ = v___x_3076_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3698_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3699_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v___x_3707_);
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
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_unsigned_to_nat(2u);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_r_3692_);
lean_ctor_set(v___x_3076_, 0, v___x_3721_);
v___x_3723_ = v___x_3076_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_r_3692_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v___x_3726_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_3073_);
lean_ctor_set(v___x_3076_, 0, v___x_3565_);
v___x_3726_ = v___x_3076_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3565_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3071_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3072_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_l_3073_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_l_3073_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
}
}
else
{
return v_t_3070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3730_, lean_object* v_t_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3730_, v_t_3731_);
lean_dec(v_k_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3733_, lean_object* v_x_3734_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3733_, v_x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3736_, lean_object* v_x_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3736_, v_x_3737_);
lean_dec(v_declName_3736_);
return v_res_3738_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3741_ = l_Lean_stringToMessageData(v___x_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; lean_object* v_env_3751_; lean_object* v___f_3752_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___x_3796_; 
v___x_3750_ = lean_st_ref_get(v___y_3748_);
v_env_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc_ref(v_env_3751_);
lean_dec(v___x_3750_);
lean_inc(v_declName_3742_);
v___f_3752_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3752_, 0, v_declName_3742_);
v___x_3796_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3751_, v_declName_3742_);
lean_dec_ref(v_env_3751_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_dec_ref(v___y_3743_);
lean_dec(v_declName_3742_);
v___y_3754_ = v___y_3746_;
v___y_3755_ = v___y_3748_;
goto v___jp_3753_;
}
else
{
uint8_t v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_dec_ref(v___x_3796_);
lean_dec_ref(v___f_3752_);
v___x_3797_ = 0;
v___x_3798_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3799_ = l_Lean_MessageData_ofConstName(v_declName_3742_, v___x_3797_);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3800_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v___x_3803_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3802_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3803_;
}
v___jp_3753_:
{
lean_object* v___x_3756_; lean_object* v_env_3757_; lean_object* v_nextMacroScope_3758_; lean_object* v_ngen_3759_; lean_object* v_auxDeclNGen_3760_; lean_object* v_traceState_3761_; lean_object* v_messages_3762_; lean_object* v_infoState_3763_; lean_object* v_snapshotTasks_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3794_; 
v___x_3756_ = lean_st_ref_take(v___y_3755_);
v_env_3757_ = lean_ctor_get(v___x_3756_, 0);
v_nextMacroScope_3758_ = lean_ctor_get(v___x_3756_, 1);
v_ngen_3759_ = lean_ctor_get(v___x_3756_, 2);
v_auxDeclNGen_3760_ = lean_ctor_get(v___x_3756_, 3);
v_traceState_3761_ = lean_ctor_get(v___x_3756_, 4);
v_messages_3762_ = lean_ctor_get(v___x_3756_, 6);
v_infoState_3763_ = lean_ctor_get(v___x_3756_, 7);
v_snapshotTasks_3764_ = lean_ctor_get(v___x_3756_, 8);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v___x_3756_, 5);
lean_dec(v_unused_3795_);
v___x_3766_ = v___x_3756_;
v_isShared_3767_ = v_isSharedCheck_3794_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_snapshotTasks_3764_);
lean_inc(v_infoState_3763_);
lean_inc(v_messages_3762_);
lean_inc(v_traceState_3761_);
lean_inc(v_auxDeclNGen_3760_);
lean_inc(v_ngen_3759_);
lean_inc(v_nextMacroScope_3758_);
lean_inc(v_env_3757_);
lean_dec(v___x_3756_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3794_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3768_ = l_Lean_docStringExt;
v___x_3769_ = lean_box(2);
v___x_3770_ = lean_box(0);
v___x_3771_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3768_, v_env_3757_, v___f_3752_, v___x_3769_, v___x_3770_);
v___x_3772_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 5, v___x_3772_);
lean_ctor_set(v___x_3766_, 0, v___x_3771_);
v___x_3774_ = v___x_3766_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3771_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_nextMacroScope_3758_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_ngen_3759_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_auxDeclNGen_3760_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v_traceState_3761_);
lean_ctor_set(v_reuseFailAlloc_3793_, 5, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3793_, 6, v_messages_3762_);
lean_ctor_set(v_reuseFailAlloc_3793_, 7, v_infoState_3763_);
lean_ctor_set(v_reuseFailAlloc_3793_, 8, v_snapshotTasks_3764_);
v___x_3774_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v_mctx_3777_; lean_object* v_zetaDeltaFVarIds_3778_; lean_object* v_postponed_3779_; lean_object* v_diag_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3791_; 
v___x_3775_ = lean_st_ref_set(v___y_3755_, v___x_3774_);
v___x_3776_ = lean_st_ref_take(v___y_3754_);
v_mctx_3777_ = lean_ctor_get(v___x_3776_, 0);
v_zetaDeltaFVarIds_3778_ = lean_ctor_get(v___x_3776_, 2);
v_postponed_3779_ = lean_ctor_get(v___x_3776_, 3);
v_diag_3780_ = lean_ctor_get(v___x_3776_, 4);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; 
v_unused_3792_ = lean_ctor_get(v___x_3776_, 1);
lean_dec(v_unused_3792_);
v___x_3782_ = v___x_3776_;
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_diag_3780_);
lean_inc(v_postponed_3779_);
lean_inc(v_zetaDeltaFVarIds_3778_);
lean_inc(v_mctx_3777_);
lean_dec(v___x_3776_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3791_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
v___x_3784_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3783_ == 0)
{
lean_ctor_set(v___x_3782_, 1, v___x_3784_);
v___x_3786_ = v___x_3782_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_mctx_3777_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_zetaDeltaFVarIds_3778_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_postponed_3779_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_diag_3780_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_st_ref_set(v___y_3754_, v___x_3786_);
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
return v_res_3812_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
return v___x_3815_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3818_ = l_Lean_stringToMessageData(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3821_ = l_Lean_stringToMessageData(v___x_3820_);
return v___x_3821_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3824_ = l_Lean_stringToMessageData(v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v___x_3833_; lean_object* v_env_3834_; uint8_t v___x_3835_; lean_object* v___x_3836_; 
v___x_3833_ = lean_st_ref_get(v_a_3831_);
v_env_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc_ref(v_env_3834_);
lean_dec(v___x_3833_);
v___x_3835_ = 1;
lean_inc(v_declName_3825_);
v___x_3836_ = l_Lean_findInternalDocString_x3f(v_env_3834_, v_declName_3825_, v___x_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
if (lean_obj_tag(v_a_3837_) == 1)
{
lean_object* v_val_3838_; 
v_val_3838_ = lean_ctor_get(v_a_3837_, 0);
lean_inc(v_val_3838_);
lean_dec_ref(v_a_3837_);
if (lean_obj_tag(v_val_3838_) == 0)
{
lean_object* v_val_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3861_; 
v_val_3839_ = lean_ctor_get(v_val_3838_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_val_3838_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3841_ = v_val_3838_;
v_isShared_3842_ = v_isSharedCheck_3861_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_val_3839_);
lean_dec(v_val_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3861_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_removeBuiltinDocString(v_declName_3825_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v___x_3844_; 
lean_dec_ref(v___x_3843_);
lean_del_object(v___x_3841_);
lean_inc_ref(v_a_3826_);
lean_inc(v_declName_3825_);
v___x_3844_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v___x_3845_; 
lean_dec_ref(v___x_3844_);
v___x_3845_ = l_Lean_addVersoDocStringFromString(v_declName_3825_, v_val_3839_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
return v___x_3845_;
}
else
{
lean_dec(v_val_3839_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_declName_3825_);
return v___x_3844_;
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_val_3839_);
lean_dec(v_a_3831_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_declName_3825_);
v_a_3846_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3848_ = v___x_3843_;
v_isShared_3849_ = v_isSharedCheck_3860_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3843_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3860_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_ref_3850_; lean_object* v___x_3851_; lean_object* v___x_3853_; 
v_ref_3850_ = lean_ctor_get(v_a_3830_, 5);
lean_inc(v_ref_3850_);
lean_dec_ref(v_a_3830_);
v___x_3851_ = lean_io_error_to_string(v_a_3846_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set_tag(v___x_3841_, 3);
lean_ctor_set(v___x_3841_, 0, v___x_3851_);
v___x_3853_ = v___x_3841_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3854_ = l_Lean_MessageData_ofFormat(v___x_3853_);
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v_ref_3850_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3855_);
v___x_3857_ = v___x_3848_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
}
else
{
lean_object* v___x_3862_; uint8_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_dec(v_val_3838_);
v___x_3862_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3863_ = 0;
v___x_3864_ = l_Lean_MessageData_ofConstName(v_declName_3825_, v___x_3863_);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3862_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3865_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
v___x_3868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3867_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
return v___x_3868_;
}
}
else
{
lean_object* v___x_3869_; uint8_t v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec(v_a_3837_);
v___x_3869_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3870_ = 0;
v___x_3871_ = l_Lean_MessageData_ofConstName(v_declName_3825_, v___x_3870_);
v___x_3872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3869_);
lean_ctor_set(v___x_3872_, 1, v___x_3871_);
v___x_3873_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3874_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
return v___x_3875_;
}
}
else
{
lean_object* v_a_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3831_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
lean_dec_ref(v_a_3826_);
lean_dec(v_declName_3825_);
v_a_3876_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3878_ = v___x_3836_;
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_a_3876_);
lean_dec(v___x_3836_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3888_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v_ref_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
v_ref_3880_ = lean_ctor_get(v_a_3830_, 5);
lean_inc(v_ref_3880_);
lean_dec_ref(v_a_3830_);
v___x_3881_ = lean_io_error_to_string(v_a_3876_);
v___x_3882_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = l_Lean_MessageData_ofFormat(v___x_3882_);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v_ref_3880_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v___x_3884_);
v___x_3886_ = v___x_3878_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_makeDocStringVerso(v_declName_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3898_, lean_object* v_k_3899_, lean_object* v_t_3900_, lean_object* v_h_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3899_, v_t_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3903_, lean_object* v_k_3904_, lean_object* v_t_3905_, lean_object* v_h_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3903_, v_k_3904_, v_t_3905_, v_h_3906_);
lean_dec(v_k_3904_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3908_, lean_object* v_binders_3909_, lean_object* v_docComment_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v_options_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; 
v_options_3918_ = lean_ctor_get(v_a_3915_, 2);
v___x_3919_ = l_Lean_doc_verso;
v___x_3920_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_3918_, v___x_3919_);
v___x_3921_ = l_Lean_addDocStringOf(v___x_3920_, v_declName_3908_, v_binders_3909_, v_docComment_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3922_, lean_object* v_binders_3923_, lean_object* v_docComment_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_addDocString(v_declName_3922_, v_binders_3923_, v_docComment_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3933_, lean_object* v_binders_3934_, lean_object* v_docString_x3f_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3935_) == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_binders_3934_);
lean_dec(v_declName_3933_);
v___x_3943_ = lean_box(0);
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
else
{
lean_object* v_val_3945_; lean_object* v___x_3946_; 
v_val_3945_ = lean_ctor_get(v_docString_x3f_3935_, 0);
lean_inc(v_val_3945_);
lean_dec_ref(v_docString_x3f_3935_);
v___x_3946_ = l_Lean_addDocString(v_declName_3933_, v_binders_3934_, v_val_3945_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
return v___x_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3947_, lean_object* v_binders_3948_, lean_object* v_docString_x3f_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_addDocString_x27(v_declName_3947_, v_binders_3948_, v_docString_x3f_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v___x_3962_; lean_object* v_nextMacroScope_3963_; lean_object* v_ngen_3964_; lean_object* v_auxDeclNGen_3965_; lean_object* v_traceState_3966_; lean_object* v_messages_3967_; lean_object* v_infoState_3968_; lean_object* v_snapshotTasks_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3995_; 
v___x_3962_ = lean_st_ref_take(v___y_3960_);
v_nextMacroScope_3963_ = lean_ctor_get(v___x_3962_, 1);
v_ngen_3964_ = lean_ctor_get(v___x_3962_, 2);
v_auxDeclNGen_3965_ = lean_ctor_get(v___x_3962_, 3);
v_traceState_3966_ = lean_ctor_get(v___x_3962_, 4);
v_messages_3967_ = lean_ctor_get(v___x_3962_, 6);
v_infoState_3968_ = lean_ctor_get(v___x_3962_, 7);
v_snapshotTasks_3969_ = lean_ctor_get(v___x_3962_, 8);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; lean_object* v_unused_3997_; 
v_unused_3996_ = lean_ctor_get(v___x_3962_, 5);
lean_dec(v_unused_3996_);
v_unused_3997_ = lean_ctor_get(v___x_3962_, 0);
lean_dec(v_unused_3997_);
v___x_3971_ = v___x_3962_;
v_isShared_3972_ = v_isSharedCheck_3995_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_snapshotTasks_3969_);
lean_inc(v_infoState_3968_);
lean_inc(v_messages_3967_);
lean_inc(v_traceState_3966_);
lean_inc(v_auxDeclNGen_3965_);
lean_inc(v_ngen_3964_);
lean_inc(v_nextMacroScope_3963_);
lean_dec(v___x_3962_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3995_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 5, v___x_3973_);
lean_ctor_set(v___x_3971_, 0, v_env_3958_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_env_3958_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_nextMacroScope_3963_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_ngen_3964_);
lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_auxDeclNGen_3965_);
lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_traceState_3966_);
lean_ctor_set(v_reuseFailAlloc_3994_, 5, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3994_, 6, v_messages_3967_);
lean_ctor_set(v_reuseFailAlloc_3994_, 7, v_infoState_3968_);
lean_ctor_set(v_reuseFailAlloc_3994_, 8, v_snapshotTasks_3969_);
v___x_3975_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v_mctx_3978_; lean_object* v_zetaDeltaFVarIds_3979_; lean_object* v_postponed_3980_; lean_object* v_diag_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3992_; 
v___x_3976_ = lean_st_ref_set(v___y_3960_, v___x_3975_);
v___x_3977_ = lean_st_ref_take(v___y_3959_);
v_mctx_3978_ = lean_ctor_get(v___x_3977_, 0);
v_zetaDeltaFVarIds_3979_ = lean_ctor_get(v___x_3977_, 2);
v_postponed_3980_ = lean_ctor_get(v___x_3977_, 3);
v_diag_3981_ = lean_ctor_get(v___x_3977_, 4);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; 
v_unused_3993_ = lean_ctor_get(v___x_3977_, 1);
lean_dec(v_unused_3993_);
v___x_3983_ = v___x_3977_;
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_diag_3981_);
lean_inc(v_postponed_3980_);
lean_inc(v_zetaDeltaFVarIds_3979_);
lean_inc(v_mctx_3978_);
lean_dec(v___x_3977_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3992_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 1, v___x_3985_);
v___x_3987_ = v___x_3983_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_mctx_3978_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v_zetaDeltaFVarIds_3979_);
lean_ctor_set(v_reuseFailAlloc_3991_, 3, v_postponed_3980_);
lean_ctor_set(v_reuseFailAlloc_3991_, 4, v_diag_3981_);
v___x_3987_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v___x_3988_ = lean_st_ref_set(v___y_3959_, v___x_3987_);
v___x_3989_ = lean_box(0);
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3998_, v___y_3999_, v___y_4000_);
lean_dec(v___y_4000_);
lean_dec(v___y_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; lean_object* v_env_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4011_ = lean_st_ref_get(v___y_4009_);
v_env_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc_ref(v_env_4012_);
lean_dec(v___x_4011_);
v___x_4013_ = l_Lean_getMainModuleDoc(v_env_4012_);
v___x_4014_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4013_);
lean_dec_ref(v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec_ref(v_docs_4003_);
v___x_4015_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4016_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4015_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; lean_object* v_env_4018_; lean_object* v___x_4019_; 
v___x_4017_ = lean_st_ref_get(v___y_4009_);
v_env_4018_ = lean_ctor_get(v___x_4017_, 0);
lean_inc_ref(v_env_4018_);
lean_dec(v___x_4017_);
v___x_4019_ = l_Lean_addVersoModuleDocSnippet(v_env_4018_, v_docs_4003_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4019_);
v___x_4021_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_4022_ = l_Lean_stringToMessageData(v_a_4020_);
v___x_4023_ = l_Lean_indentD(v___x_4022_);
v___x_4024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4021_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
v___x_4025_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4024_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4025_;
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4027_; 
lean_dec_ref(v___y_4004_);
v_a_4026_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4026_);
lean_dec_ref(v___x_4019_);
v___x_4027_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4026_, v___y_4007_, v___y_4009_);
return v___x_4027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4037_, lean_object* v_docComment_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v___x_4046_; 
lean_inc(v_a_4044_);
lean_inc_ref(v_a_4043_);
lean_inc(v_a_4042_);
lean_inc_ref(v_a_4041_);
lean_inc(v_a_4040_);
lean_inc_ref(v_a_4039_);
v___x_4046_ = l_Lean_versoModDocString(v_range_4037_, v_docComment_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref(v___x_4046_);
v___x_4048_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_a_4047_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_);
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
return v___x_4048_;
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_4044_);
lean_dec_ref(v_a_4043_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
v_a_4049_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4046_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4046_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4057_, lean_object* v_docComment_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_addVersoModDocString(v_range_4057_, v_docComment_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_docComment_4058_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4067_, v___y_4071_, v___y_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
return v_res_4084_;
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
