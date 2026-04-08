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
uint8_t v___x_1931__boxed_176_; lean_object* v_res_177_; 
v___x_1931__boxed_176_ = lean_unbox(v___x_171_);
v_res_177_ = l_Lean_parseVersoDocString___redArg___lam__3(v_text_168_, v_fst_169_, v_snd_170_, v___x_1931__boxed_176_, v_logMessage_172_, v_toBind_173_, v___f_174_, v_____do__lift_175_);
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
uint8_t v___x_1965__boxed_202_; lean_object* v_res_203_; 
v___x_1965__boxed_202_ = lean_unbox(v___x_194_);
v_res_203_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_193_, v___x_1965__boxed_202_, v_logMessage_195_, v_toBind_196_, v___f_197_, v_getFileName_198_, v_a_199_, v_x_200_, v___y_201_);
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
uint8_t v___x_1995__boxed_237_; lean_object* v_res_238_; 
v___x_1995__boxed_237_ = lean_unbox(v___x_232_);
v_res_238_ = l_Lean_parseVersoDocString___redArg___lam__5(v_text_229_, v_pos_230_, v_source_231_, v___x_1995__boxed_237_, v_logMessage_233_, v_toBind_234_, v___f_235_, v_____do__lift_236_);
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
lean_dec(v_pre_488_);
lean_dec_ref(v_pre_487_);
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
lean_dec(v_pre_486_);
lean_dec_ref(v_pre_485_);
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
lean_dec(v_pre_485_);
lean_dec_ref(v_kind_484_);
lean_dec_ref(v___x_483_);
lean_dec_ref(v_toApplicative_470_);
v___x_527_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_483_);
lean_dec(v_kind_484_);
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
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v___x_567_, lean_object* v_toPure_568_, lean_object* v_____r_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_567_);
v___x_571_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v_text_572_, lean_object* v_fst_573_, lean_object* v_snd_574_, lean_object* v_logMessage_575_, lean_object* v_toBind_576_, lean_object* v___f_577_, lean_object* v_____do__lift_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_579_ = l_Lean_FileMap_toPosition(v_text_572_, v_fst_573_);
v___x_580_ = lean_box(0);
v___x_581_ = 0;
v___x_582_ = 2;
v___x_583_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_584_ = l_Lean_Parser_Error_toString(v_snd_574_);
v___x_585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
v___x_586_ = l_Lean_MessageData_ofFormat(v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_587_, 0, v_____do__lift_578_);
lean_ctor_set(v___x_587_, 1, v___x_579_);
lean_ctor_set(v___x_587_, 2, v___x_580_);
lean_ctor_set(v___x_587_, 3, v___x_583_);
lean_ctor_set(v___x_587_, 4, v___x_586_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*5, v___x_581_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*5 + 1, v___x_582_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*5 + 2, v___x_581_);
v___x_588_ = lean_apply_1(v_logMessage_575_, v___x_587_);
v___x_589_ = lean_apply_4(v_toBind_576_, lean_box(0), lean_box(0), v___x_588_, v___f_577_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2___boxed(lean_object* v_text_590_, lean_object* v_fst_591_, lean_object* v_snd_592_, lean_object* v_logMessage_593_, lean_object* v_toBind_594_, lean_object* v___f_595_, lean_object* v_____do__lift_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_reportVersoParseFailure___redArg___lam__2(v_text_590_, v_fst_591_, v_snd_592_, v_logMessage_593_, v_toBind_594_, v___f_595_, v_____do__lift_596_);
lean_dec(v_fst_591_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_text_598_, lean_object* v_logMessage_599_, lean_object* v_toBind_600_, lean_object* v___f_601_, lean_object* v_getFileName_602_, lean_object* v_a_603_, lean_object* v_x_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_snd_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v_snd_606_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_606_);
v_fst_607_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_fst_607_);
lean_dec_ref(v_a_603_);
v_snd_608_ = lean_ctor_get(v_snd_606_, 1);
lean_inc(v_snd_608_);
lean_dec(v_snd_606_);
lean_inc(v_toBind_600_);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2___boxed), 7, 6);
lean_closure_set(v___f_609_, 0, v_text_598_);
lean_closure_set(v___f_609_, 1, v_fst_607_);
lean_closure_set(v___f_609_, 2, v_snd_608_);
lean_closure_set(v___f_609_, 3, v_logMessage_599_);
lean_closure_set(v___f_609_, 4, v_toBind_600_);
lean_closure_set(v___f_609_, 5, v___f_601_);
v___x_610_ = lean_apply_4(v_toBind_600_, lean_box(0), lean_box(0), v_getFileName_602_, v___f_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_toPure_611_, lean_object* v___x_612_, lean_object* v_toBind_613_, lean_object* v_getFileName_614_, lean_object* v___f_615_, lean_object* v___x_616_, lean_object* v___x_617_, lean_object* v___y_618_, lean_object* v_ictx_619_, lean_object* v_____s_620_){
_start:
{
uint8_t v___y_622_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = lean_array_get_size(v___x_616_);
v___x_626_ = lean_nat_dec_eq(v___x_625_, v___x_617_);
if (v___x_626_ == 0)
{
v___y_622_ = v___x_626_;
goto v___jp_621_;
}
else
{
lean_object* v_pos_627_; uint8_t v___x_628_; 
v_pos_627_ = lean_ctor_get(v___y_618_, 2);
v___x_628_ = l_Lean_Parser_InputContext_atEnd(v_ictx_619_, v_pos_627_);
if (v___x_628_ == 0)
{
v___y_622_ = v___x_626_;
goto v___jp_621_;
}
else
{
lean_object* v___x_629_; 
lean_dec(v___f_615_);
lean_dec(v_getFileName_614_);
lean_dec(v_toBind_613_);
v___x_629_ = lean_apply_2(v_toPure_611_, lean_box(0), v___x_612_);
return v___x_629_;
}
}
v___jp_621_:
{
if (v___y_622_ == 0)
{
lean_object* v___x_623_; 
lean_dec(v___f_615_);
lean_dec(v_getFileName_614_);
lean_dec(v_toBind_613_);
v___x_623_ = lean_apply_2(v_toPure_611_, lean_box(0), v___x_612_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; 
lean_dec(v_toPure_611_);
v___x_624_ = lean_apply_4(v_toBind_613_, lean_box(0), lean_box(0), v_getFileName_614_, v___f_615_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4___boxed(lean_object* v_toPure_630_, lean_object* v___x_631_, lean_object* v_toBind_632_, lean_object* v_getFileName_633_, lean_object* v___f_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___y_637_, lean_object* v_ictx_638_, lean_object* v_____s_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_reportVersoParseFailure___redArg___lam__4(v_toPure_630_, v___x_631_, v_toBind_632_, v_getFileName_633_, v___f_634_, v___x_635_, v___x_636_, v___y_637_, v_ictx_638_, v_____s_639_);
lean_dec_ref(v_ictx_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___x_636_);
lean_dec_ref(v___x_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_text_641_, lean_object* v_source_642_, lean_object* v_logMessage_643_, lean_object* v_toPure_644_, lean_object* v_toBind_645_, lean_object* v_getFileName_646_, lean_object* v___x_647_, lean_object* v_ictx_648_, lean_object* v_inst_649_, lean_object* v_env_650_, lean_object* v_____do__lift_651_, lean_object* v_____do__lift_652_, lean_object* v_val_653_, lean_object* v___y_654_, lean_object* v_____do__lift_655_){
_start:
{
lean_object* v___y_657_; lean_object* v_pmctx_668_; lean_object* v_blockCtxt_669_; lean_object* v___x_670_; lean_object* v_s_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_s_674_; uint8_t v___y_676_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
lean_inc_ref(v_env_650_);
v_pmctx_668_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_668_, 0, v_env_650_);
lean_ctor_set(v_pmctx_668_, 1, v_____do__lift_651_);
lean_ctor_set(v_pmctx_668_, 2, v_____do__lift_652_);
lean_ctor_set(v_pmctx_668_, 3, v_____do__lift_655_);
lean_inc(v_val_653_);
lean_inc_ref(v_text_641_);
v_blockCtxt_669_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_641_, v_val_653_, v___y_654_);
v___x_670_ = l_Lean_Parser_mkParserState(v_source_642_);
lean_inc_ref(v___x_670_);
v_s_671_ = l_Lean_Parser_ParserState_setPos(v___x_670_, v_val_653_);
v___x_672_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_672_, 0, v_blockCtxt_669_);
v___x_673_ = l_Lean_Parser_getTokenTable(v_env_650_);
lean_inc_ref(v___x_673_);
lean_inc_ref(v_pmctx_668_);
lean_inc_ref(v_ictx_648_);
v_s_674_ = l_Lean_Parser_ParserFn_run(v___x_672_, v_ictx_648_, v_pmctx_668_, v___x_673_, v_s_671_);
lean_inc_ref(v_s_674_);
v___x_686_ = l_Lean_Parser_ParserState_allErrors(v_s_674_);
v___x_687_ = lean_array_get_size(v___x_686_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_nat_dec_eq(v___x_687_, v___x_647_);
if (v___x_688_ == 0)
{
v___y_676_ = v___x_688_;
goto v___jp_675_;
}
else
{
lean_object* v_pos_689_; uint8_t v___x_690_; 
v_pos_689_ = lean_ctor_get(v_s_674_, 2);
lean_inc(v_pos_689_);
v___x_690_ = l_Lean_Parser_InputContext_atEnd(v_ictx_648_, v_pos_689_);
lean_dec(v_pos_689_);
if (v___x_690_ == 0)
{
v___y_676_ = v___x_688_;
goto v___jp_675_;
}
else
{
lean_dec_ref(v___x_673_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v_pmctx_668_);
v___y_657_ = v_s_674_;
goto v___jp_656_;
}
}
v___jp_656_:
{
lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___f_663_; size_t v_sz_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc(v_logMessage_643_);
lean_inc_ref(v_text_641_);
lean_inc_ref_n(v___y_657_, 2);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_658_, 0, v___y_657_);
lean_closure_set(v___f_658_, 1, v_text_641_);
lean_closure_set(v___f_658_, 2, v_source_642_);
lean_closure_set(v___f_658_, 3, v_logMessage_643_);
v___x_659_ = l_Lean_Parser_ParserState_allErrors(v___y_657_);
v___x_660_ = lean_box(0);
lean_inc(v_toPure_644_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1), 3, 2);
lean_closure_set(v___f_661_, 0, v___x_660_);
lean_closure_set(v___f_661_, 1, v_toPure_644_);
lean_inc(v_getFileName_646_);
lean_inc_n(v_toBind_645_, 2);
v___f_662_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 8, 5);
lean_closure_set(v___f_662_, 0, v_text_641_);
lean_closure_set(v___f_662_, 1, v_logMessage_643_);
lean_closure_set(v___f_662_, 2, v_toBind_645_);
lean_closure_set(v___f_662_, 3, v___f_661_);
lean_closure_set(v___f_662_, 4, v_getFileName_646_);
lean_inc_ref(v___x_659_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_663_, 0, v_toPure_644_);
lean_closure_set(v___f_663_, 1, v___x_660_);
lean_closure_set(v___f_663_, 2, v_toBind_645_);
lean_closure_set(v___f_663_, 3, v_getFileName_646_);
lean_closure_set(v___f_663_, 4, v___f_658_);
lean_closure_set(v___f_663_, 5, v___x_659_);
lean_closure_set(v___f_663_, 6, v___x_647_);
lean_closure_set(v___f_663_, 7, v___y_657_);
lean_closure_set(v___f_663_, 8, v_ictx_648_);
v_sz_664_ = lean_array_size(v___x_659_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_649_, v___x_659_, v___f_662_, v_sz_664_, v___x_665_, v___x_660_);
v___x_667_ = lean_apply_4(v_toBind_645_, lean_box(0), lean_box(0), v___x_666_, v___f_663_);
return v___x_667_;
}
v___jp_675_:
{
if (v___y_676_ == 0)
{
lean_dec_ref(v___x_673_);
lean_dec_ref(v___x_670_);
lean_dec_ref(v_pmctx_668_);
v___y_657_ = v_s_674_;
goto v___jp_656_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_pos_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_677_ = lean_box(0);
v___x_678_ = lean_box(0);
v___x_679_ = lean_unsigned_to_nat(1u);
lean_inc_n(v___x_647_, 3);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
lean_ctor_set(v___x_680_, 1, v___x_647_);
v___x_681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_681_, 0, v___x_647_);
lean_ctor_set(v___x_681_, 1, v___x_677_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
lean_ctor_set(v___x_681_, 3, v___x_680_);
lean_ctor_set(v___x_681_, 4, v___x_647_);
v_pos_682_ = lean_ctor_get(v_s_674_, 2);
lean_inc(v_pos_682_);
lean_dec_ref(v_s_674_);
v___x_683_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_683_, 0, v___x_681_);
v___x_684_ = l_Lean_Parser_ParserState_setPos(v___x_670_, v_pos_682_);
lean_inc_ref(v_ictx_648_);
v___x_685_ = l_Lean_Parser_ParserFn_run(v___x_683_, v_ictx_648_, v_pmctx_668_, v___x_673_, v___x_684_);
v___y_657_ = v___x_685_;
goto v___jp_656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_text_691_, lean_object* v_source_692_, lean_object* v_logMessage_693_, lean_object* v_toPure_694_, lean_object* v_toBind_695_, lean_object* v_getFileName_696_, lean_object* v___x_697_, lean_object* v_ictx_698_, lean_object* v_inst_699_, lean_object* v_env_700_, lean_object* v_____do__lift_701_, lean_object* v_val_702_, lean_object* v___y_703_, lean_object* v_getOpenDecls_704_, lean_object* v_____do__lift_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
lean_inc(v_toBind_695_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(v___f_706_, 0, v_text_691_);
lean_closure_set(v___f_706_, 1, v_source_692_);
lean_closure_set(v___f_706_, 2, v_logMessage_693_);
lean_closure_set(v___f_706_, 3, v_toPure_694_);
lean_closure_set(v___f_706_, 4, v_toBind_695_);
lean_closure_set(v___f_706_, 5, v_getFileName_696_);
lean_closure_set(v___f_706_, 6, v___x_697_);
lean_closure_set(v___f_706_, 7, v_ictx_698_);
lean_closure_set(v___f_706_, 8, v_inst_699_);
lean_closure_set(v___f_706_, 9, v_env_700_);
lean_closure_set(v___f_706_, 10, v_____do__lift_701_);
lean_closure_set(v___f_706_, 11, v_____do__lift_705_);
lean_closure_set(v___f_706_, 12, v_val_702_);
lean_closure_set(v___f_706_, 13, v___y_703_);
v___x_707_ = lean_apply_4(v_toBind_695_, lean_box(0), lean_box(0), v_getOpenDecls_704_, v___f_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_708_, lean_object* v_text_709_, lean_object* v_source_710_, lean_object* v_logMessage_711_, lean_object* v_toPure_712_, lean_object* v_toBind_713_, lean_object* v_getFileName_714_, lean_object* v___x_715_, lean_object* v_ictx_716_, lean_object* v_inst_717_, lean_object* v_env_718_, lean_object* v_val_719_, lean_object* v___y_720_, lean_object* v_____do__lift_721_){
_start:
{
lean_object* v_getCurrNamespace_722_; lean_object* v_getOpenDecls_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v_getCurrNamespace_722_ = lean_ctor_get(v_inst_708_, 0);
lean_inc(v_getCurrNamespace_722_);
v_getOpenDecls_723_ = lean_ctor_get(v_inst_708_, 1);
lean_inc(v_getOpenDecls_723_);
lean_dec_ref(v_inst_708_);
lean_inc(v_toBind_713_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 15, 14);
lean_closure_set(v___f_724_, 0, v_text_709_);
lean_closure_set(v___f_724_, 1, v_source_710_);
lean_closure_set(v___f_724_, 2, v_logMessage_711_);
lean_closure_set(v___f_724_, 3, v_toPure_712_);
lean_closure_set(v___f_724_, 4, v_toBind_713_);
lean_closure_set(v___f_724_, 5, v_getFileName_714_);
lean_closure_set(v___f_724_, 6, v___x_715_);
lean_closure_set(v___f_724_, 7, v_ictx_716_);
lean_closure_set(v___f_724_, 8, v_inst_717_);
lean_closure_set(v___f_724_, 9, v_env_718_);
lean_closure_set(v___f_724_, 10, v_____do__lift_721_);
lean_closure_set(v___f_724_, 11, v_val_719_);
lean_closure_set(v___f_724_, 12, v___y_720_);
lean_closure_set(v___f_724_, 13, v_getOpenDecls_723_);
v___x_725_ = lean_apply_4(v_toBind_713_, lean_box(0), lean_box(0), v_getCurrNamespace_722_, v___f_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_source_726_, lean_object* v_text_727_, lean_object* v___y_728_, lean_object* v_inst_729_, lean_object* v_logMessage_730_, lean_object* v_toPure_731_, lean_object* v_toBind_732_, lean_object* v_getFileName_733_, lean_object* v___x_734_, lean_object* v_inst_735_, lean_object* v_env_736_, lean_object* v_val_737_, lean_object* v_inst_738_, lean_object* v_____do__lift_739_){
_start:
{
lean_object* v_ictx_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
lean_inc(v___y_728_);
lean_inc_ref(v_text_727_);
lean_inc_ref(v_source_726_);
v_ictx_740_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_740_, 0, v_source_726_);
lean_ctor_set(v_ictx_740_, 1, v_____do__lift_739_);
lean_ctor_set(v_ictx_740_, 2, v_text_727_);
lean_ctor_set(v_ictx_740_, 3, v___y_728_);
lean_inc(v_toBind_732_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 14, 13);
lean_closure_set(v___f_741_, 0, v_inst_729_);
lean_closure_set(v___f_741_, 1, v_text_727_);
lean_closure_set(v___f_741_, 2, v_source_726_);
lean_closure_set(v___f_741_, 3, v_logMessage_730_);
lean_closure_set(v___f_741_, 4, v_toPure_731_);
lean_closure_set(v___f_741_, 5, v_toBind_732_);
lean_closure_set(v___f_741_, 6, v_getFileName_733_);
lean_closure_set(v___f_741_, 7, v___x_734_);
lean_closure_set(v___f_741_, 8, v_ictx_740_);
lean_closure_set(v___f_741_, 9, v_inst_735_);
lean_closure_set(v___f_741_, 10, v_env_736_);
lean_closure_set(v___f_741_, 11, v_val_737_);
lean_closure_set(v___f_741_, 12, v___y_728_);
v___x_742_ = lean_apply_4(v_toBind_732_, lean_box(0), lean_box(0), v_inst_738_, v___f_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object* v_inst_743_, lean_object* v_source_744_, lean_object* v_text_745_, lean_object* v___y_746_, lean_object* v_inst_747_, lean_object* v_toPure_748_, lean_object* v_toBind_749_, lean_object* v___x_750_, lean_object* v_inst_751_, lean_object* v_val_752_, lean_object* v_inst_753_, lean_object* v_env_754_){
_start:
{
lean_object* v_getFileName_755_; lean_object* v_logMessage_756_; lean_object* v___f_757_; lean_object* v___x_758_; 
v_getFileName_755_ = lean_ctor_get(v_inst_743_, 2);
lean_inc_n(v_getFileName_755_, 2);
v_logMessage_756_ = lean_ctor_get(v_inst_743_, 4);
lean_inc(v_logMessage_756_);
lean_dec_ref(v_inst_743_);
lean_inc(v_toBind_749_);
v___f_757_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 14, 13);
lean_closure_set(v___f_757_, 0, v_source_744_);
lean_closure_set(v___f_757_, 1, v_text_745_);
lean_closure_set(v___f_757_, 2, v___y_746_);
lean_closure_set(v___f_757_, 3, v_inst_747_);
lean_closure_set(v___f_757_, 4, v_logMessage_756_);
lean_closure_set(v___f_757_, 5, v_toPure_748_);
lean_closure_set(v___f_757_, 6, v_toBind_749_);
lean_closure_set(v___f_757_, 7, v_getFileName_755_);
lean_closure_set(v___f_757_, 8, v___x_750_);
lean_closure_set(v___f_757_, 9, v_inst_751_);
lean_closure_set(v___f_757_, 10, v_env_754_);
lean_closure_set(v___f_757_, 11, v_val_752_);
lean_closure_set(v___f_757_, 12, v_inst_753_);
v___x_758_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v_getFileName_755_, v___f_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__10(lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_toPure_762_, lean_object* v_toBind_763_, lean_object* v___x_764_, lean_object* v_inst_765_, lean_object* v_val_766_, lean_object* v_inst_767_, lean_object* v_val_768_, lean_object* v_text_769_){
_start:
{
lean_object* v_source_770_; lean_object* v___y_772_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_source_770_ = lean_ctor_get(v_text_769_, 0);
lean_inc_ref(v_source_770_);
v___x_776_ = lean_string_utf8_byte_size(v_source_770_);
v___x_777_ = lean_nat_dec_le(v_val_768_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v_val_768_);
v___y_772_ = v___x_776_;
goto v___jp_771_;
}
else
{
v___y_772_ = v_val_768_;
goto v___jp_771_;
}
v___jp_771_:
{
lean_object* v_getEnv_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_getEnv_773_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_getEnv_773_);
lean_dec_ref(v_inst_759_);
lean_inc(v_toBind_763_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__9), 12, 11);
lean_closure_set(v___f_774_, 0, v_inst_760_);
lean_closure_set(v___f_774_, 1, v_source_770_);
lean_closure_set(v___f_774_, 2, v_text_769_);
lean_closure_set(v___f_774_, 3, v___y_772_);
lean_closure_set(v___f_774_, 4, v_inst_761_);
lean_closure_set(v___f_774_, 5, v_toPure_762_);
lean_closure_set(v___f_774_, 6, v_toBind_763_);
lean_closure_set(v___f_774_, 7, v___x_764_);
lean_closure_set(v___f_774_, 8, v_inst_765_);
lean_closure_set(v___f_774_, 9, v_val_766_);
lean_closure_set(v___f_774_, 10, v_inst_767_);
v___x_775_ = lean_apply_4(v_toBind_763_, lean_box(0), lean_box(0), v_getEnv_773_, v___f_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_parseFailure_784_){
_start:
{
lean_object* v_toApplicative_785_; lean_object* v_toBind_786_; lean_object* v_toPure_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v_toApplicative_785_ = lean_ctor_get(v_inst_778_, 0);
v_toBind_786_ = lean_ctor_get(v_inst_778_, 1);
lean_inc(v_toBind_786_);
v_toPure_787_ = lean_ctor_get(v_toApplicative_785_, 1);
lean_inc(v_toPure_787_);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = l_Lean_Syntax_getArg(v_parseFailure_784_, v___x_788_);
v___x_790_ = 1;
v___x_791_ = l_Lean_Syntax_getPos_x3f(v___x_789_, v___x_790_);
if (lean_obj_tag(v___x_791_) == 1)
{
lean_object* v_val_792_; lean_object* v___x_793_; 
v_val_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_val_792_);
lean_dec_ref(v___x_791_);
v___x_793_ = l_Lean_Syntax_getTailPos_x3f(v___x_789_, v___x_790_);
lean_dec(v___x_789_);
if (lean_obj_tag(v___x_793_) == 1)
{
lean_object* v_val_794_; lean_object* v___f_795_; lean_object* v___x_796_; 
v_val_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v___x_793_);
lean_inc(v_toBind_786_);
v___f_795_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__10), 11, 10);
lean_closure_set(v___f_795_, 0, v_inst_780_);
lean_closure_set(v___f_795_, 1, v_inst_782_);
lean_closure_set(v___f_795_, 2, v_inst_783_);
lean_closure_set(v___f_795_, 3, v_toPure_787_);
lean_closure_set(v___f_795_, 4, v_toBind_786_);
lean_closure_set(v___f_795_, 5, v___x_788_);
lean_closure_set(v___f_795_, 6, v_inst_778_);
lean_closure_set(v___f_795_, 7, v_val_792_);
lean_closure_set(v___f_795_, 8, v_inst_781_);
lean_closure_set(v___f_795_, 9, v_val_794_);
v___x_796_ = lean_apply_4(v_toBind_786_, lean_box(0), lean_box(0), v_inst_779_, v___f_795_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___x_793_);
lean_dec(v_val_792_);
lean_dec(v_toBind_786_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_inst_782_);
lean_dec(v_inst_781_);
lean_dec_ref(v_inst_780_);
lean_dec(v_inst_779_);
lean_dec_ref(v_inst_778_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_apply_2(v_toPure_787_, lean_box(0), v___x_797_);
return v___x_798_;
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v___x_791_);
lean_dec(v___x_789_);
lean_dec(v_toBind_786_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_inst_782_);
lean_dec(v_inst_781_);
lean_dec_ref(v_inst_780_);
lean_dec(v_inst_779_);
lean_dec_ref(v_inst_778_);
v___x_799_ = lean_box(0);
v___x_800_ = lean_apply_2(v_toPure_787_, lean_box(0), v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_parseFailure_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_reportVersoParseFailure___redArg(v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_, v_inst_806_, v_parseFailure_807_);
lean_dec(v_parseFailure_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_parseFailure_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_reportVersoParseFailure___redArg(v_inst_810_, v_inst_811_, v_inst_813_, v_inst_814_, v_inst_815_, v_inst_816_, v_parseFailure_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_parseFailure_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_reportVersoParseFailure(v_m_819_, v_inst_820_, v_inst_821_, v_inst_822_, v_inst_823_, v_inst_824_, v_inst_825_, v_inst_826_, v_parseFailure_827_);
lean_dec(v_parseFailure_827_);
lean_dec_ref(v_inst_822_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_829_, size_t v_i_830_, lean_object* v_bs_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_lt(v_i_830_, v_sz_829_);
if (v___x_832_ == 0)
{
return v_bs_831_;
}
else
{
lean_object* v_v_833_; lean_object* v___x_834_; lean_object* v_bs_x27_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v_v_833_ = lean_array_uget(v_bs_831_, v_i_830_);
v___x_834_ = lean_unsigned_to_nat(0u);
v_bs_x27_835_ = lean_array_uset(v_bs_831_, v_i_830_, v___x_834_);
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_add(v_i_830_, v___x_836_);
v___x_838_ = lean_array_uset(v_bs_x27_835_, v_i_830_, v_v_833_);
v_i_830_ = v___x_837_;
v_bs_831_ = v___x_838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_840_, lean_object* v_i_841_, lean_object* v_bs_842_){
_start:
{
size_t v_sz_boxed_843_; size_t v_i_boxed_844_; lean_object* v_res_845_; 
v_sz_boxed_843_ = lean_unbox_usize(v_sz_840_);
lean_dec(v_sz_840_);
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_843_, v_i_boxed_844_, v_bs_842_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v___x_854_, uint8_t v_suppressElabErrors_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 1)
{
lean_object* v_pre_857_; 
v_pre_857_ = lean_ctor_get(v_x_856_, 0);
switch(lean_obj_tag(v_pre_857_))
{
case 1:
{
lean_object* v_pre_858_; 
v_pre_858_ = lean_ctor_get(v_pre_857_, 0);
switch(lean_obj_tag(v_pre_858_))
{
case 0:
{
lean_object* v_str_859_; lean_object* v_str_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v_str_859_ = lean_ctor_get(v_x_856_, 1);
v_str_860_ = lean_ctor_get(v_pre_857_, 1);
v___x_861_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_862_ = lean_string_dec_eq(v_str_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_864_ = lean_string_dec_eq(v_str_860_, v___x_863_);
if (v___x_864_ == 0)
{
return v___x_854_;
}
else
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_866_ = lean_string_dec_eq(v_str_859_, v___x_865_);
if (v___x_866_ == 0)
{
return v___x_854_;
}
else
{
return v_suppressElabErrors_855_;
}
}
}
else
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_868_ = lean_string_dec_eq(v_str_859_, v___x_867_);
if (v___x_868_ == 0)
{
return v___x_854_;
}
else
{
return v_suppressElabErrors_855_;
}
}
}
case 1:
{
lean_object* v_pre_869_; 
v_pre_869_ = lean_ctor_get(v_pre_858_, 0);
if (lean_obj_tag(v_pre_869_) == 0)
{
lean_object* v_str_870_; lean_object* v_str_871_; lean_object* v_str_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_str_870_ = lean_ctor_get(v_x_856_, 1);
v_str_871_ = lean_ctor_get(v_pre_857_, 1);
v_str_872_ = lean_ctor_get(v_pre_858_, 1);
v___x_873_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_874_ = lean_string_dec_eq(v_str_872_, v___x_873_);
if (v___x_874_ == 0)
{
return v___x_854_;
}
else
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_876_ = lean_string_dec_eq(v_str_871_, v___x_875_);
if (v___x_876_ == 0)
{
return v___x_854_;
}
else
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_878_ = lean_string_dec_eq(v_str_870_, v___x_877_);
if (v___x_878_ == 0)
{
return v___x_854_;
}
else
{
return v_suppressElabErrors_855_;
}
}
}
}
else
{
return v___x_854_;
}
}
default: 
{
return v___x_854_;
}
}
}
case 0:
{
lean_object* v_str_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_str_879_ = lean_ctor_get(v_x_856_, 1);
v___x_880_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_881_ = lean_string_dec_eq(v_str_879_, v___x_880_);
if (v___x_881_ == 0)
{
return v___x_854_;
}
else
{
return v_suppressElabErrors_855_;
}
}
default: 
{
return v___x_854_;
}
}
}
else
{
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v___x_882_, lean_object* v_suppressElabErrors_883_, lean_object* v_x_884_){
_start:
{
uint8_t v___x_10525__boxed_885_; uint8_t v_suppressElabErrors_boxed_886_; uint8_t v_res_887_; lean_object* v_r_888_; 
v___x_10525__boxed_885_ = lean_unbox(v___x_882_);
v_suppressElabErrors_boxed_886_ = lean_unbox(v_suppressElabErrors_883_);
v_res_887_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_10525__boxed_885_, v_suppressElabErrors_boxed_886_, v_x_884_);
lean_dec(v_x_884_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v___x_889_, uint8_t v_suppressElabErrors_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 1)
{
lean_object* v_pre_892_; 
v_pre_892_ = lean_ctor_get(v_x_891_, 0);
switch(lean_obj_tag(v_pre_892_))
{
case 1:
{
lean_object* v_pre_893_; 
v_pre_893_ = lean_ctor_get(v_pre_892_, 0);
switch(lean_obj_tag(v_pre_893_))
{
case 0:
{
lean_object* v_str_894_; lean_object* v_str_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_str_894_ = lean_ctor_get(v_x_891_, 1);
v_str_895_ = lean_ctor_get(v_pre_892_, 1);
v___x_896_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_897_ = lean_string_dec_eq(v_str_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_899_ = lean_string_dec_eq(v_str_895_, v___x_898_);
if (v___x_899_ == 0)
{
return v___x_889_;
}
else
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_901_ = lean_string_dec_eq(v_str_894_, v___x_900_);
if (v___x_901_ == 0)
{
return v___x_889_;
}
else
{
return v_suppressElabErrors_890_;
}
}
}
else
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_903_ = lean_string_dec_eq(v_str_894_, v___x_902_);
if (v___x_903_ == 0)
{
return v___x_889_;
}
else
{
return v_suppressElabErrors_890_;
}
}
}
case 1:
{
lean_object* v_pre_904_; 
v_pre_904_ = lean_ctor_get(v_pre_893_, 0);
if (lean_obj_tag(v_pre_904_) == 0)
{
lean_object* v_str_905_; lean_object* v_str_906_; lean_object* v_str_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_str_905_ = lean_ctor_get(v_x_891_, 1);
v_str_906_ = lean_ctor_get(v_pre_892_, 1);
v_str_907_ = lean_ctor_get(v_pre_893_, 1);
v___x_908_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_909_ = lean_string_dec_eq(v_str_907_, v___x_908_);
if (v___x_909_ == 0)
{
return v___x_889_;
}
else
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_911_ = lean_string_dec_eq(v_str_906_, v___x_910_);
if (v___x_911_ == 0)
{
return v___x_889_;
}
else
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_913_ = lean_string_dec_eq(v_str_905_, v___x_912_);
if (v___x_913_ == 0)
{
return v___x_889_;
}
else
{
return v_suppressElabErrors_890_;
}
}
}
}
else
{
return v___x_889_;
}
}
default: 
{
return v___x_889_;
}
}
}
case 0:
{
lean_object* v_str_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_str_914_ = lean_ctor_get(v_x_891_, 1);
v___x_915_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_916_ = lean_string_dec_eq(v_str_914_, v___x_915_);
if (v___x_916_ == 0)
{
return v___x_889_;
}
else
{
return v_suppressElabErrors_890_;
}
}
default: 
{
return v___x_889_;
}
}
}
else
{
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___x_917_, lean_object* v_suppressElabErrors_918_, lean_object* v_x_919_){
_start:
{
uint8_t v___x_10597__boxed_920_; uint8_t v_suppressElabErrors_boxed_921_; uint8_t v_res_922_; lean_object* v_r_923_; 
v___x_10597__boxed_920_ = lean_unbox(v___x_917_);
v_suppressElabErrors_boxed_921_ = lean_unbox(v_suppressElabErrors_918_);
v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_10597__boxed_920_, v_suppressElabErrors_boxed_921_, v_x_919_);
lean_dec(v_x_919_);
v_r_923_ = lean_box(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_a_934_; uint8_t v___x_938_; 
v___x_938_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v___x_924_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_929_);
return v___x_939_;
}
else
{
lean_object* v_a_940_; lean_object* v_snd_941_; lean_object* v_fst_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_999_; 
v_a_940_ = lean_array_uget(v_as_926_, v_i_928_);
v_snd_941_ = lean_ctor_get(v_a_940_, 1);
v_fst_942_ = lean_ctor_get(v_a_940_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_999_ == 0)
{
v___x_944_ = v_a_940_;
v_isShared_945_ = v_isSharedCheck_999_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_snd_941_);
lean_inc(v_fst_942_);
lean_dec(v_a_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_999_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_snd_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_997_; 
v_snd_946_ = lean_ctor_get(v_snd_941_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_snd_941_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_snd_941_, 0);
lean_dec(v_unused_998_);
v___x_948_ = v_snd_941_;
v_isShared_949_ = v_isSharedCheck_997_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_snd_946_);
lean_dec(v_snd_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_997_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_fileName_950_; uint8_t v_suppressElabErrors_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___y_963_; lean_object* v___y_964_; 
v_fileName_950_ = lean_ctor_get(v___y_930_, 0);
v_suppressElabErrors_951_ = lean_ctor_get_uint8(v___y_930_, sizeof(void*)*14 + 1);
v___x_952_ = lean_box(0);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_nat_dec_eq(v___x_925_, v___x_953_);
lean_inc_ref(v___x_924_);
v___x_955_ = l_Lean_FileMap_toPosition(v___x_924_, v_fst_942_);
lean_dec(v_fst_942_);
v___x_956_ = lean_box(0);
v___x_957_ = 2;
v___x_958_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_959_ = l_Lean_Parser_Error_toString(v_snd_946_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
v___x_961_ = l_Lean_MessageData_ofFormat(v___x_960_);
if (v_suppressElabErrors_951_ == 0)
{
v___y_963_ = v___y_930_;
v___y_964_ = v___y_931_;
goto v___jp_962_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___f_995_; uint8_t v___x_996_; 
v___x_993_ = lean_box(v___x_954_);
v___x_994_ = lean_box(v_suppressElabErrors_951_);
v___f_995_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_995_, 0, v___x_993_);
lean_closure_set(v___f_995_, 1, v___x_994_);
lean_inc_ref(v___x_961_);
v___x_996_ = l_Lean_MessageData_hasTag(v___f_995_, v___x_961_);
if (v___x_996_ == 0)
{
lean_dec_ref(v___x_961_);
lean_dec_ref(v___x_955_);
lean_del_object(v___x_948_);
lean_del_object(v___x_944_);
v_a_934_ = v___x_952_;
goto v___jp_933_;
}
else
{
v___y_963_ = v___y_930_;
v___y_964_ = v___y_931_;
goto v___jp_962_;
}
}
v___jp_962_:
{
lean_object* v___x_965_; lean_object* v_currNamespace_966_; lean_object* v_openDecls_967_; lean_object* v___x_969_; 
v___x_965_ = lean_st_ref_take(v___y_964_);
v_currNamespace_966_ = lean_ctor_get(v___y_963_, 6);
v_openDecls_967_ = lean_ctor_get(v___y_963_, 7);
lean_inc(v_openDecls_967_);
lean_inc(v_currNamespace_966_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_openDecls_967_);
lean_ctor_set(v___x_948_, 0, v_currNamespace_966_);
v___x_969_ = v___x_948_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_currNamespace_966_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_openDecls_967_);
v___x_969_ = v_reuseFailAlloc_992_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 4);
lean_ctor_set(v___x_944_, 1, v___x_961_);
lean_ctor_set(v___x_944_, 0, v___x_969_);
v___x_971_ = v___x_944_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_961_);
v___x_971_ = v_reuseFailAlloc_991_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v_env_973_; lean_object* v_nextMacroScope_974_; lean_object* v_ngen_975_; lean_object* v_auxDeclNGen_976_; lean_object* v_traceState_977_; lean_object* v_cache_978_; lean_object* v_messages_979_; lean_object* v_infoState_980_; lean_object* v_snapshotTasks_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
lean_inc_ref(v_fileName_950_);
v___x_972_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_972_, 0, v_fileName_950_);
lean_ctor_set(v___x_972_, 1, v___x_955_);
lean_ctor_set(v___x_972_, 2, v___x_956_);
lean_ctor_set(v___x_972_, 3, v___x_958_);
lean_ctor_set(v___x_972_, 4, v___x_971_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*5, v___x_954_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*5 + 1, v___x_957_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*5 + 2, v___x_954_);
v_env_973_ = lean_ctor_get(v___x_965_, 0);
v_nextMacroScope_974_ = lean_ctor_get(v___x_965_, 1);
v_ngen_975_ = lean_ctor_get(v___x_965_, 2);
v_auxDeclNGen_976_ = lean_ctor_get(v___x_965_, 3);
v_traceState_977_ = lean_ctor_get(v___x_965_, 4);
v_cache_978_ = lean_ctor_get(v___x_965_, 5);
v_messages_979_ = lean_ctor_get(v___x_965_, 6);
v_infoState_980_ = lean_ctor_get(v___x_965_, 7);
v_snapshotTasks_981_ = lean_ctor_get(v___x_965_, 8);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v___x_965_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snapshotTasks_981_);
lean_inc(v_infoState_980_);
lean_inc(v_messages_979_);
lean_inc(v_cache_978_);
lean_inc(v_traceState_977_);
lean_inc(v_auxDeclNGen_976_);
lean_inc(v_ngen_975_);
lean_inc(v_nextMacroScope_974_);
lean_inc(v_env_973_);
lean_dec(v___x_965_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_985_ = l_Lean_MessageLog_add(v___x_972_, v_messages_979_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 6, v___x_985_);
v___x_987_ = v___x_983_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_env_973_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_nextMacroScope_974_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_ngen_975_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_auxDeclNGen_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_traceState_977_);
lean_ctor_set(v_reuseFailAlloc_989_, 5, v_cache_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 6, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_989_, 7, v_infoState_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 8, v_snapshotTasks_981_);
v___x_987_ = v_reuseFailAlloc_989_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_st_ref_set(v___y_964_, v___x_987_);
v_a_934_ = v___x_952_;
goto v___jp_933_;
}
}
}
}
}
}
}
}
v___jp_933_:
{
size_t v___x_935_; size_t v___x_936_; 
v___x_935_ = ((size_t)1ULL);
v___x_936_ = lean_usize_add(v_i_928_, v___x_935_);
v_i_928_ = v___x_936_;
v_b_929_ = v_a_934_;
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
lean_inc_n(v_macroStack_1129_, 2);
v___x_1130_ = l_Lean_Elab_getBetterRef(v_ref_1126_, v_macroStack_1129_);
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
lean_object* v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; uint8_t v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; uint8_t v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; uint8_t v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
lean_inc(v_docComment_1188_);
v___x_1361_ = l_Lean_Syntax_getKind(v_docComment_1188_);
v___x_1362_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_1363_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_1364_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_1365_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_1366_ = lean_name_eq(v___x_1361_, v___x_1365_);
lean_dec(v___x_1361_);
if (v___x_1366_ == 0)
{
goto v___jp_1338_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = l_Lean_Syntax_getArg(v_docComment_1188_, v___x_1367_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_kind_1369_; 
v_kind_1369_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_kind_1369_);
if (lean_obj_tag(v_kind_1369_) == 1)
{
lean_object* v_pre_1370_; 
v_pre_1370_ = lean_ctor_get(v_kind_1369_, 0);
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
if (lean_obj_tag(v_pre_1372_) == 1)
{
lean_object* v_pre_1373_; 
v_pre_1373_ = lean_ctor_get(v_pre_1372_, 0);
lean_inc(v_pre_1373_);
if (lean_obj_tag(v_pre_1373_) == 0)
{
lean_object* v_info_1374_; lean_object* v_args_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1401_; 
v_info_1374_ = lean_ctor_get(v___x_1368_, 0);
v_args_1375_ = lean_ctor_get(v___x_1368_, 2);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1368_, 1);
lean_dec(v_unused_1402_);
v___x_1377_ = v___x_1368_;
v_isShared_1378_ = v_isSharedCheck_1401_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_args_1375_);
lean_inc(v_info_1374_);
lean_dec(v___x_1368_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1401_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_str_1379_; lean_object* v_str_1380_; lean_object* v_str_1381_; lean_object* v_str_1382_; uint8_t v___x_1383_; 
v_str_1379_ = lean_ctor_get(v_kind_1369_, 1);
lean_inc_ref(v_str_1379_);
lean_dec_ref(v_kind_1369_);
v_str_1380_ = lean_ctor_get(v_pre_1370_, 1);
lean_inc_ref(v_str_1380_);
lean_dec_ref(v_pre_1370_);
v_str_1381_ = lean_ctor_get(v_pre_1371_, 1);
lean_inc_ref(v_str_1381_);
lean_dec_ref(v_pre_1371_);
v_str_1382_ = lean_ctor_get(v_pre_1372_, 1);
lean_inc_ref(v_str_1382_);
lean_dec_ref(v_pre_1372_);
v___x_1383_ = lean_string_dec_eq(v_str_1382_, v___x_1362_);
lean_dec_ref(v_str_1382_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_str_1381_);
lean_dec_ref(v_str_1380_);
lean_dec_ref(v_str_1379_);
lean_del_object(v___x_1377_);
lean_dec_ref(v_args_1375_);
lean_dec(v_info_1374_);
goto v___jp_1338_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = lean_string_dec_eq(v_str_1381_, v___x_1363_);
lean_dec_ref(v_str_1381_);
if (v___x_1384_ == 0)
{
lean_dec_ref(v_str_1380_);
lean_dec_ref(v_str_1379_);
lean_del_object(v___x_1377_);
lean_dec_ref(v_args_1375_);
lean_dec(v_info_1374_);
goto v___jp_1338_;
}
else
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_string_dec_eq(v_str_1380_, v___x_1364_);
lean_dec_ref(v_str_1380_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_str_1379_);
lean_del_object(v___x_1377_);
lean_dec_ref(v_args_1375_);
lean_dec(v_info_1374_);
goto v___jp_1338_;
}
else
{
lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1386_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_1387_ = lean_string_dec_eq(v_str_1379_, v___x_1386_);
lean_dec_ref(v_str_1379_);
if (v___x_1387_ == 0)
{
lean_del_object(v___x_1377_);
lean_dec_ref(v_args_1375_);
lean_dec(v_info_1374_);
goto v___jp_1338_;
}
else
{
lean_dec(v_docComment_1188_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_del_object(v___x_1377_);
lean_dec_ref(v_args_1375_);
lean_dec(v_info_1374_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1390_ = l_Lean_Name_str___override(v_pre_1373_, v___x_1362_);
v___x_1391_ = l_Lean_Name_str___override(v___x_1390_, v___x_1363_);
v___x_1392_ = l_Lean_Name_str___override(v___x_1391_, v___x_1364_);
v___x_1393_ = l_Lean_Name_str___override(v___x_1392_, v___x_1386_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1393_);
v___x_1395_ = v___x_1377_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_info_1374_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_args_1375_);
v___x_1395_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = l_Lean_Syntax_getArg(v___x_1395_, v___x_1396_);
lean_dec_ref(v___x_1395_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
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
lean_dec(v_pre_1373_);
lean_dec_ref(v_pre_1372_);
lean_dec_ref(v_pre_1371_);
lean_dec_ref(v_pre_1370_);
lean_dec_ref(v_kind_1369_);
lean_dec_ref(v___x_1368_);
goto v___jp_1338_;
}
}
else
{
lean_dec(v_pre_1372_);
lean_dec_ref(v_pre_1371_);
lean_dec_ref(v_pre_1370_);
lean_dec_ref(v_kind_1369_);
lean_dec_ref(v___x_1368_);
goto v___jp_1338_;
}
}
else
{
lean_dec_ref(v_pre_1370_);
lean_dec(v_pre_1371_);
lean_dec_ref(v_kind_1369_);
lean_dec_ref(v___x_1368_);
goto v___jp_1338_;
}
}
else
{
lean_dec(v_pre_1370_);
lean_dec_ref(v_kind_1369_);
lean_dec_ref(v___x_1368_);
goto v___jp_1338_;
}
}
else
{
lean_dec_ref(v___x_1368_);
lean_dec(v_kind_1369_);
goto v___jp_1338_;
}
}
else
{
lean_dec(v___x_1368_);
goto v___jp_1338_;
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
lean_object* v___x_1209_; lean_object* v_currNamespace_1210_; lean_object* v_openDecls_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_env_1215_; lean_object* v_nextMacroScope_1216_; lean_object* v_ngen_1217_; lean_object* v_auxDeclNGen_1218_; lean_object* v_traceState_1219_; lean_object* v_cache_1220_; lean_object* v_messages_1221_; lean_object* v_infoState_1222_; lean_object* v_snapshotTasks_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1232_; 
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
lean_ctor_set(v___x_1213_, 1, v___y_1205_);
lean_inc(v___y_1206_);
lean_inc_ref(v___y_1203_);
v___x_1214_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1214_, 0, v___y_1203_);
lean_ctor_set(v___x_1214_, 1, v___y_1200_);
lean_ctor_set(v___x_1214_, 2, v___y_1206_);
lean_ctor_set(v___x_1214_, 3, v___y_1202_);
lean_ctor_set(v___x_1214_, 4, v___x_1213_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5, v___y_1201_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5 + 1, v___y_1204_);
lean_ctor_set_uint8(v___x_1214_, sizeof(void*)*5 + 2, v___y_1201_);
v_env_1215_ = lean_ctor_get(v___x_1209_, 0);
v_nextMacroScope_1216_ = lean_ctor_get(v___x_1209_, 1);
v_ngen_1217_ = lean_ctor_get(v___x_1209_, 2);
v_auxDeclNGen_1218_ = lean_ctor_get(v___x_1209_, 3);
v_traceState_1219_ = lean_ctor_get(v___x_1209_, 4);
v_cache_1220_ = lean_ctor_get(v___x_1209_, 5);
v_messages_1221_ = lean_ctor_get(v___x_1209_, 6);
v_infoState_1222_ = lean_ctor_get(v___x_1209_, 7);
v_snapshotTasks_1223_ = lean_ctor_get(v___x_1209_, 8);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1225_ = v___x_1209_;
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
else
{
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
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1232_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = l_Lean_MessageLog_add(v___x_1214_, v_messages_1221_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 6, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_env_1215_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_nextMacroScope_1216_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_ngen_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_auxDeclNGen_1218_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_traceState_1219_);
lean_ctor_set(v_reuseFailAlloc_1231_, 5, v_cache_1220_);
lean_ctor_set(v_reuseFailAlloc_1231_, 6, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1231_, 7, v_infoState_1222_);
lean_ctor_set(v_reuseFailAlloc_1231_, 8, v_snapshotTasks_1223_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_st_ref_set(v___y_1208_, v___x_1229_);
goto v___jp_1196_;
}
}
}
v___jp_1233_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
lean_inc_ref(v___y_1240_);
v___x_1241_ = l_Lean_Parser_ParserState_allErrors(v___y_1240_);
v___x_1242_ = lean_array_get_size(v___x_1241_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_nat_dec_eq(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; 
lean_dec_ref(v___y_1240_);
lean_dec_ref(v___y_1239_);
v___x_1245_ = lean_box(0);
v_sz_1246_ = lean_array_size(v___x_1241_);
v___x_1247_ = ((size_t)0ULL);
lean_inc_ref(v___y_1235_);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1235_, v___x_1242_, v___x_1241_, v_sz_1246_, v___x_1247_, v___x_1245_, v___y_1193_, v___y_1194_);
lean_dec_ref(v___x_1241_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1256_; 
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1257_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1256_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1248_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1248_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_stxStack_1266_; lean_object* v_pos_1267_; uint8_t v___x_1268_; 
lean_dec_ref(v___x_1241_);
v_stxStack_1266_ = lean_ctor_get(v___y_1240_, 0);
lean_inc_ref(v_stxStack_1266_);
v_pos_1267_ = lean_ctor_get(v___y_1240_, 2);
lean_inc(v_pos_1267_);
lean_dec_ref(v___y_1240_);
v___x_1268_ = l_Lean_Parser_InputContext_atEnd(v___y_1239_, v_pos_1267_);
lean_dec_ref(v___y_1239_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; uint32_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v_stxStack_1266_);
lean_inc_ref(v___y_1235_);
v___x_1269_ = l_Lean_FileMap_toPosition(v___y_1235_, v_pos_1267_);
v___x_1270_ = lean_box(0);
v___x_1271_ = 2;
v___x_1272_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1273_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1274_ = lean_string_utf8_get(v___y_1238_, v_pos_1267_);
lean_dec(v_pos_1267_);
v___x_1275_ = lean_string_push(v___x_1272_, v___x_1274_);
v___x_1276_ = lean_string_append(v___x_1273_, v___x_1275_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1278_ = lean_string_append(v___x_1276_, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
v___x_1280_ = l_Lean_MessageData_ofFormat(v___x_1279_);
if (v___y_1237_ == 0)
{
v___y_1200_ = v___x_1269_;
v___y_1201_ = v___x_1268_;
v___y_1202_ = v___x_1272_;
v___y_1203_ = v___y_1236_;
v___y_1204_ = v___x_1271_;
v___y_1205_ = v___x_1280_;
v___y_1206_ = v___x_1270_;
v___y_1207_ = v___y_1193_;
v___y_1208_ = v___y_1194_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; uint8_t v___x_1284_; 
v___x_1281_ = lean_box(v___x_1268_);
v___x_1282_ = lean_box(v___y_1234_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1283_, 0, v___x_1281_);
lean_closure_set(v___f_1283_, 1, v___x_1282_);
lean_inc_ref(v___x_1280_);
v___x_1284_ = l_Lean_MessageData_hasTag(v___f_1283_, v___x_1280_);
if (v___x_1284_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v___x_1269_);
goto v___jp_1196_;
}
else
{
v___y_1200_ = v___x_1269_;
v___y_1201_ = v___x_1268_;
v___y_1202_ = v___x_1272_;
v___y_1203_ = v___y_1236_;
v___y_1204_ = v___x_1271_;
v___y_1205_ = v___x_1280_;
v___y_1206_ = v___x_1270_;
v___y_1207_ = v___y_1193_;
v___y_1208_ = v___y_1194_;
goto v___jp_1199_;
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_pos_1267_);
v___x_1285_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1266_);
lean_dec_ref(v_stxStack_1266_);
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1286_);
return v___x_1287_;
}
}
}
v___jp_1288_:
{
if (v___y_1300_ == 0)
{
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v___y_1295_);
v___y_1234_ = v___y_1289_;
v___y_1235_ = v___y_1290_;
v___y_1236_ = v___y_1291_;
v___y_1237_ = v___y_1292_;
v___y_1238_ = v___y_1293_;
v___y_1239_ = v___y_1294_;
v___y_1240_ = v___y_1299_;
goto v___jp_1233_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_pos_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___y_1298_);
lean_ctor_set(v___x_1304_, 1, v___x_1301_);
v___x_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1301_);
lean_ctor_set(v___x_1305_, 1, v___x_1302_);
lean_ctor_set(v___x_1305_, 2, v___x_1303_);
lean_ctor_set(v___x_1305_, 3, v___x_1304_);
lean_ctor_set(v___x_1305_, 4, v___x_1301_);
v_pos_1306_ = lean_ctor_get(v___y_1299_, 2);
lean_inc(v_pos_1306_);
lean_dec_ref(v___y_1299_);
v___x_1307_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_1307_, 0, v___x_1305_);
v___x_1308_ = l_Lean_Parser_ParserState_setPos(v___y_1297_, v_pos_1306_);
lean_inc_ref(v___y_1294_);
v___x_1309_ = l_Lean_Parser_ParserFn_run(v___x_1307_, v___y_1294_, v___y_1296_, v___y_1295_, v___x_1308_);
v___y_1234_ = v___y_1289_;
v___y_1235_ = v___y_1290_;
v___y_1236_ = v___y_1291_;
v___y_1237_ = v___y_1292_;
v___y_1238_ = v___y_1293_;
v___y_1239_ = v___y_1294_;
v___y_1240_ = v___x_1309_;
goto v___jp_1233_;
}
}
v___jp_1310_:
{
lean_object* v___x_1322_; lean_object* v_env_1323_; lean_object* v_ictx_1324_; lean_object* v_pmctx_1325_; lean_object* v_blockCtxt_1326_; lean_object* v___x_1327_; lean_object* v_s_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_s_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1322_ = lean_st_ref_get(v___y_1194_);
v_env_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_ref_n(v_env_1323_, 2);
lean_dec(v___x_1322_);
lean_inc(v___y_1321_);
lean_inc_ref_n(v___y_1316_, 2);
lean_inc_ref(v___y_1318_);
lean_inc_ref(v___y_1312_);
v_ictx_1324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1324_, 0, v___y_1312_);
lean_ctor_set(v_ictx_1324_, 1, v___y_1318_);
lean_ctor_set(v_ictx_1324_, 2, v___y_1316_);
lean_ctor_set(v_ictx_1324_, 3, v___y_1321_);
lean_inc(v___y_1313_);
lean_inc(v___y_1317_);
lean_inc_ref(v___y_1315_);
v_pmctx_1325_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1325_, 0, v_env_1323_);
lean_ctor_set(v_pmctx_1325_, 1, v___y_1315_);
lean_ctor_set(v_pmctx_1325_, 2, v___y_1317_);
lean_ctor_set(v_pmctx_1325_, 3, v___y_1313_);
lean_inc(v___y_1314_);
v_blockCtxt_1326_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1316_, v___y_1314_, v___y_1321_);
v___x_1327_ = l_Lean_Parser_mkParserState(v___y_1312_);
lean_inc_ref(v___x_1327_);
v_s_1328_ = l_Lean_Parser_ParserState_setPos(v___x_1327_, v___y_1314_);
v___x_1329_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_1329_, 0, v_blockCtxt_1326_);
v___x_1330_ = l_Lean_Parser_getTokenTable(v_env_1323_);
lean_inc_ref(v___x_1330_);
lean_inc_ref(v_pmctx_1325_);
lean_inc_ref(v_ictx_1324_);
v_s_1331_ = l_Lean_Parser_ParserFn_run(v___x_1329_, v_ictx_1324_, v_pmctx_1325_, v___x_1330_, v_s_1328_);
lean_inc_ref(v_s_1331_);
v___x_1332_ = l_Lean_Parser_ParserState_allErrors(v_s_1331_);
v___x_1333_ = lean_array_get_size(v___x_1332_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_nat_dec_eq(v___x_1333_, v___x_1334_);
if (v___x_1335_ == 0)
{
v___y_1289_ = v___y_1311_;
v___y_1290_ = v___y_1316_;
v___y_1291_ = v___y_1318_;
v___y_1292_ = v___y_1319_;
v___y_1293_ = v___y_1312_;
v___y_1294_ = v_ictx_1324_;
v___y_1295_ = v___x_1330_;
v___y_1296_ = v_pmctx_1325_;
v___y_1297_ = v___x_1327_;
v___y_1298_ = v___y_1320_;
v___y_1299_ = v_s_1331_;
v___y_1300_ = v___x_1335_;
goto v___jp_1288_;
}
else
{
lean_object* v_pos_1336_; uint8_t v___x_1337_; 
v_pos_1336_ = lean_ctor_get(v_s_1331_, 2);
lean_inc(v_pos_1336_);
v___x_1337_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1324_, v_pos_1336_);
lean_dec(v_pos_1336_);
if (v___x_1337_ == 0)
{
v___y_1289_ = v___y_1311_;
v___y_1290_ = v___y_1316_;
v___y_1291_ = v___y_1318_;
v___y_1292_ = v___y_1319_;
v___y_1293_ = v___y_1312_;
v___y_1294_ = v_ictx_1324_;
v___y_1295_ = v___x_1330_;
v___y_1296_ = v_pmctx_1325_;
v___y_1297_ = v___x_1327_;
v___y_1298_ = v___y_1320_;
v___y_1299_ = v_s_1331_;
v___y_1300_ = v___x_1335_;
goto v___jp_1288_;
}
else
{
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1327_);
lean_dec_ref(v_pmctx_1325_);
lean_dec(v___y_1320_);
v___y_1234_ = v___y_1311_;
v___y_1235_ = v___y_1316_;
v___y_1236_ = v___y_1318_;
v___y_1237_ = v___y_1319_;
v___y_1238_ = v___y_1312_;
v___y_1239_ = v_ictx_1324_;
v___y_1240_ = v_s_1331_;
goto v___jp_1233_;
}
}
}
v___jp_1338_:
{
lean_object* v_fileName_1339_; lean_object* v_fileMap_1340_; lean_object* v_options_1341_; lean_object* v_currNamespace_1342_; lean_object* v_openDecls_1343_; uint8_t v_suppressElabErrors_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; 
v_fileName_1339_ = lean_ctor_get(v___y_1193_, 0);
v_fileMap_1340_ = lean_ctor_get(v___y_1193_, 1);
v_options_1341_ = lean_ctor_get(v___y_1193_, 2);
v_currNamespace_1342_ = lean_ctor_get(v___y_1193_, 6);
v_openDecls_1343_ = lean_ctor_get(v___y_1193_, 7);
v_suppressElabErrors_1344_ = lean_ctor_get_uint8(v___y_1193_, sizeof(void*)*14 + 1);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = l_Lean_Syntax_getArg(v_docComment_1188_, v___x_1345_);
v___x_1347_ = 1;
v___x_1348_ = l_Lean_Syntax_getPos_x3f(v___x_1346_, v___x_1347_);
if (lean_obj_tag(v___x_1348_) == 1)
{
lean_object* v_val_1349_; lean_object* v___x_1350_; 
v_val_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_val_1349_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = l_Lean_Syntax_getTailPos_x3f(v___x_1346_, v___x_1347_);
lean_dec(v___x_1346_);
if (lean_obj_tag(v___x_1350_) == 1)
{
lean_object* v_val_1351_; lean_object* v_source_1352_; lean_object* v___x_1353_; lean_object* v_endPos_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
lean_dec(v_docComment_1188_);
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref(v___x_1350_);
v_source_1352_ = lean_ctor_get(v_fileMap_1340_, 0);
v___x_1353_ = lean_string_utf8_prev(v_source_1352_, v_val_1351_);
lean_dec(v_val_1351_);
v_endPos_1354_ = lean_string_utf8_prev(v_source_1352_, v___x_1353_);
lean_dec(v___x_1353_);
v___x_1355_ = lean_string_utf8_byte_size(v_source_1352_);
v___x_1356_ = lean_nat_dec_le(v_endPos_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_dec(v_endPos_1354_);
v___y_1311_ = v_suppressElabErrors_1344_;
v___y_1312_ = v_source_1352_;
v___y_1313_ = v_openDecls_1343_;
v___y_1314_ = v_val_1349_;
v___y_1315_ = v_options_1341_;
v___y_1316_ = v_fileMap_1340_;
v___y_1317_ = v_currNamespace_1342_;
v___y_1318_ = v_fileName_1339_;
v___y_1319_ = v_suppressElabErrors_1344_;
v___y_1320_ = v___x_1345_;
v___y_1321_ = v___x_1355_;
goto v___jp_1310_;
}
else
{
v___y_1311_ = v_suppressElabErrors_1344_;
v___y_1312_ = v_source_1352_;
v___y_1313_ = v_openDecls_1343_;
v___y_1314_ = v_val_1349_;
v___y_1315_ = v_options_1341_;
v___y_1316_ = v_fileMap_1340_;
v___y_1317_ = v_currNamespace_1342_;
v___y_1318_ = v_fileName_1339_;
v___y_1319_ = v_suppressElabErrors_1344_;
v___y_1320_ = v___x_1345_;
v___y_1321_ = v_endPos_1354_;
goto v___jp_1310_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v___x_1350_);
lean_dec(v_val_1349_);
v___x_1357_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1358_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1188_, v___x_1357_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v_docComment_1188_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v___x_1348_);
lean_dec(v___x_1346_);
v___x_1359_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_1360_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1188_, v___x_1359_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v_docComment_1188_);
return v___x_1360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1416_, lean_object* v_binders_1417_, lean_object* v_docComment_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1443_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1443_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1443_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
if (lean_obj_tag(v_a_1427_) == 1)
{
lean_object* v_val_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; 
lean_del_object(v___x_1429_);
v_val_1431_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_val_1431_);
lean_dec_ref(v_a_1427_);
v___x_1432_ = l_Lean_Syntax_getArgs(v_val_1431_);
lean_dec(v_val_1431_);
v_sz_1433_ = lean_array_size(v___x_1432_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_1433_, v___x_1434_, v___x_1432_);
v___x_1436_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1436_, 0, v___x_1435_);
v___x_1437_ = 0;
v___x_1438_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1416_, v_binders_1417_, v___x_1436_, v___x_1437_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec(v_a_1427_);
lean_dec(v_binders_1417_);
lean_dec(v_declName_1416_);
v___x_1439_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1439_);
v___x_1441_ = v___x_1429_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_binders_1417_);
lean_dec(v_declName_1416_);
v_a_1444_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1426_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1426_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1452_, lean_object* v_binders_1453_, lean_object* v_docComment_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_versoDocString(v_declName_1452_, v_binders_1453_, v_docComment_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v_as_1465_, size_t v_sz_1466_, size_t v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1463_, v___x_1464_, v_as_1465_, v_sz_1466_, v_i_1467_, v_b_1468_, v___y_1473_, v___y_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v_as_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_1477_, v___x_1478_, v_as_1479_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec_ref(v_as_1479_);
lean_dec(v___x_1478_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_1493_, lean_object* v_ref_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1504_, lean_object* v_ref_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_1504_, v_ref_1505_, v_msg_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v_ref_1505_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1515_, lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_1525_, v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(lean_object* v_msgData_1535_, lean_object* v_macroStack_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___redArg(v_msgData_1535_, v_macroStack_1536_, v___y_1541_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5___boxed(lean_object* v_msgData_1545_, lean_object* v_macroStack_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5(v_msgData_1545_, v_macroStack_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(size_t v_sz_1555_, size_t v_i_1556_, lean_object* v_bs_1557_){
_start:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_usize_dec_lt(v_i_1556_, v_sz_1555_);
if (v___x_1558_ == 0)
{
return v_bs_1557_;
}
else
{
lean_object* v_v_1559_; lean_object* v___x_1560_; lean_object* v_bs_x27_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_v_1559_ = lean_array_uget(v_bs_1557_, v_i_1556_);
v___x_1560_ = lean_unsigned_to_nat(0u);
v_bs_x27_1561_ = lean_array_uset(v_bs_1557_, v_i_1556_, v___x_1560_);
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1556_, v___x_1562_);
v___x_1564_ = lean_array_uset(v_bs_x27_1561_, v_i_1556_, v_v_1559_);
v_i_1556_ = v___x_1563_;
v_bs_1557_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0___boxed(lean_object* v_sz_1566_, lean_object* v_i_1567_, lean_object* v_bs_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1566_);
lean_dec(v_sz_1566_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1572_, lean_object* v_doc_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1589_; lean_object* v_env_1596_; lean_object* v___x_1597_; lean_object* v_terminalNesting_1598_; 
v___x_1581_ = lean_st_ref_get(v_a_1579_);
v_env_1596_ = lean_ctor_get(v___x_1581_, 0);
lean_inc_ref(v_env_1596_);
lean_dec(v___x_1581_);
v___x_1597_ = l_Lean_getMainVersoModuleDocs(v_env_1596_);
v_terminalNesting_1598_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_terminalNesting_1598_);
lean_dec_ref(v___x_1597_);
if (lean_obj_tag(v_terminalNesting_1598_) == 0)
{
v___y_1589_ = v_terminalNesting_1598_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1608_; 
v_val_1599_ = lean_ctor_get(v_terminalNesting_1598_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_terminalNesting_1598_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1601_ = v_terminalNesting_1598_;
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_val_1599_);
lean_dec(v_terminalNesting_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1608_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1603_ = lean_unsigned_to_nat(1u);
v___x_1604_ = lean_nat_add(v_val_1599_, v___x_1603_);
lean_dec(v_val_1599_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1604_);
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v___y_1589_ = v___x_1606_;
goto v___jp_1588_;
}
}
}
v___jp_1582_:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1585_, 0, v_range_1572_);
lean_closure_set(v___x_1585_, 1, v___y_1583_);
lean_closure_set(v___x_1585_, 2, v___y_1584_);
v___x_1586_ = 0;
v___x_1587_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1585_, v___x_1586_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1587_;
}
v___jp_1588_:
{
lean_object* v___x_1590_; size_t v_sz_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = l_Lean_Syntax_getArgs(v_doc_1573_);
v_sz_1591_ = lean_array_size(v___x_1590_);
v___x_1592_ = ((size_t)0ULL);
v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_1591_, v___x_1592_, v___x_1590_);
if (lean_obj_tag(v___y_1589_) == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___y_1583_ = v___x_1593_;
v___y_1584_ = v___x_1594_;
goto v___jp_1582_;
}
else
{
lean_object* v_val_1595_; 
v_val_1595_ = lean_ctor_get(v___y_1589_, 0);
lean_inc(v_val_1595_);
lean_dec_ref(v___y_1589_);
v___y_1583_ = v___x_1593_;
v___y_1584_ = v_val_1595_;
goto v___jp_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1609_, lean_object* v_doc_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_versoModDocString(v_range_1609_, v_doc_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_doc_1610_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0(lean_object* v___x_1619_, lean_object* v_declName_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, uint8_t v___x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_fileName_1631_; lean_object* v_options_1632_; lean_object* v_currRecDepth_1633_; lean_object* v_maxRecDepth_1634_; lean_object* v_ref_1635_; lean_object* v_currNamespace_1636_; lean_object* v_openDecls_1637_; lean_object* v_initHeartbeats_1638_; lean_object* v_maxHeartbeats_1639_; lean_object* v_quotContext_1640_; lean_object* v_currMacroScope_1641_; uint8_t v_diag_1642_; lean_object* v_cancelTk_x3f_1643_; uint8_t v_suppressElabErrors_1644_; lean_object* v_inheritedTraceOptions_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_fileName_1631_ = lean_ctor_get(v___y_1628_, 0);
v_options_1632_ = lean_ctor_get(v___y_1628_, 2);
v_currRecDepth_1633_ = lean_ctor_get(v___y_1628_, 3);
v_maxRecDepth_1634_ = lean_ctor_get(v___y_1628_, 4);
v_ref_1635_ = lean_ctor_get(v___y_1628_, 5);
v_currNamespace_1636_ = lean_ctor_get(v___y_1628_, 6);
v_openDecls_1637_ = lean_ctor_get(v___y_1628_, 7);
v_initHeartbeats_1638_ = lean_ctor_get(v___y_1628_, 8);
v_maxHeartbeats_1639_ = lean_ctor_get(v___y_1628_, 9);
v_quotContext_1640_ = lean_ctor_get(v___y_1628_, 10);
v_currMacroScope_1641_ = lean_ctor_get(v___y_1628_, 11);
v_diag_1642_ = lean_ctor_get_uint8(v___y_1628_, sizeof(void*)*14);
v_cancelTk_x3f_1643_ = lean_ctor_get(v___y_1628_, 12);
v_suppressElabErrors_1644_ = lean_ctor_get_uint8(v___y_1628_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1645_ = lean_ctor_get(v___y_1628_, 13);
lean_inc_ref(v_inheritedTraceOptions_1645_);
lean_inc(v_cancelTk_x3f_1643_);
lean_inc(v_currMacroScope_1641_);
lean_inc(v_quotContext_1640_);
lean_inc(v_maxHeartbeats_1639_);
lean_inc(v_initHeartbeats_1638_);
lean_inc(v_openDecls_1637_);
lean_inc(v_currNamespace_1636_);
lean_inc(v_ref_1635_);
lean_inc(v_maxRecDepth_1634_);
lean_inc(v_currRecDepth_1633_);
lean_inc_ref(v_options_1632_);
lean_inc_ref(v_fileName_1631_);
v___x_1646_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1646_, 0, v_fileName_1631_);
lean_ctor_set(v___x_1646_, 1, v___x_1619_);
lean_ctor_set(v___x_1646_, 2, v_options_1632_);
lean_ctor_set(v___x_1646_, 3, v_currRecDepth_1633_);
lean_ctor_set(v___x_1646_, 4, v_maxRecDepth_1634_);
lean_ctor_set(v___x_1646_, 5, v_ref_1635_);
lean_ctor_set(v___x_1646_, 6, v_currNamespace_1636_);
lean_ctor_set(v___x_1646_, 7, v_openDecls_1637_);
lean_ctor_set(v___x_1646_, 8, v_initHeartbeats_1638_);
lean_ctor_set(v___x_1646_, 9, v_maxHeartbeats_1639_);
lean_ctor_set(v___x_1646_, 10, v_quotContext_1640_);
lean_ctor_set(v___x_1646_, 11, v_currMacroScope_1641_);
lean_ctor_set(v___x_1646_, 12, v_cancelTk_x3f_1643_);
lean_ctor_set(v___x_1646_, 13, v_inheritedTraceOptions_1645_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*14, v_diag_1642_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*14 + 1, v_suppressElabErrors_1644_);
v___x_1647_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1620_, v___x_1621_, v___x_1622_, v___x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___x_1646_, v___y_1629_);
lean_dec_ref(v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___lam__0___boxed(lean_object* v___x_1648_, lean_object* v_declName_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_15596__boxed_1660_; lean_object* v_res_1661_; 
v___x_15596__boxed_1660_ = lean_unbox(v___x_1652_);
v_res_1661_ = l_Lean_versoDocStringFromString___lam__0(v___x_1648_, v_declName_1649_, v___x_1650_, v___x_1651_, v___x_15596__boxed_1660_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1661_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(uint8_t v___y_1662_, uint8_t v_suppressElabErrors_1663_, lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 1)
{
lean_object* v_pre_1665_; 
v_pre_1665_ = lean_ctor_get(v_x_1664_, 0);
switch(lean_obj_tag(v_pre_1665_))
{
case 1:
{
lean_object* v_pre_1666_; 
v_pre_1666_ = lean_ctor_get(v_pre_1665_, 0);
switch(lean_obj_tag(v_pre_1666_))
{
case 0:
{
lean_object* v_str_1667_; lean_object* v_str_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_str_1667_ = lean_ctor_get(v_x_1664_, 1);
v_str_1668_ = lean_ctor_get(v_pre_1665_, 1);
v___x_1669_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__0));
v___x_1670_ = lean_string_dec_eq(v_str_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__1));
v___x_1672_ = lean_string_dec_eq(v_str_1668_, v___x_1671_);
if (v___x_1672_ == 0)
{
return v___y_1662_;
}
else
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__2));
v___x_1674_ = lean_string_dec_eq(v_str_1667_, v___x_1673_);
if (v___x_1674_ == 0)
{
return v___y_1662_;
}
else
{
return v_suppressElabErrors_1663_;
}
}
}
else
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__3));
v___x_1676_ = lean_string_dec_eq(v_str_1667_, v___x_1675_);
if (v___x_1676_ == 0)
{
return v___y_1662_;
}
else
{
return v_suppressElabErrors_1663_;
}
}
}
case 1:
{
lean_object* v_pre_1677_; 
v_pre_1677_ = lean_ctor_get(v_pre_1666_, 0);
if (lean_obj_tag(v_pre_1677_) == 0)
{
lean_object* v_str_1678_; lean_object* v_str_1679_; lean_object* v_str_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_str_1678_ = lean_ctor_get(v_x_1664_, 1);
v_str_1679_ = lean_ctor_get(v_pre_1665_, 1);
v_str_1680_ = lean_ctor_get(v_pre_1666_, 1);
v___x_1681_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__4));
v___x_1682_ = lean_string_dec_eq(v_str_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
return v___y_1662_;
}
else
{
lean_object* v___x_1683_; uint8_t v___x_1684_; 
v___x_1683_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__5));
v___x_1684_ = lean_string_dec_eq(v_str_1679_, v___x_1683_);
if (v___x_1684_ == 0)
{
return v___y_1662_;
}
else
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__6));
v___x_1686_ = lean_string_dec_eq(v_str_1678_, v___x_1685_);
if (v___x_1686_ == 0)
{
return v___y_1662_;
}
else
{
return v_suppressElabErrors_1663_;
}
}
}
}
else
{
return v___y_1662_;
}
}
default: 
{
return v___y_1662_;
}
}
}
case 0:
{
lean_object* v_str_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v_str_1687_ = lean_ctor_get(v_x_1664_, 1);
v___x_1688_ = ((lean_object*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___closed__7));
v___x_1689_ = lean_string_dec_eq(v_str_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
return v___y_1662_;
}
else
{
return v_suppressElabErrors_1663_;
}
}
default: 
{
return v___y_1662_;
}
}
}
else
{
return v___y_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed(lean_object* v___y_1690_, lean_object* v_suppressElabErrors_1691_, lean_object* v_x_1692_){
_start:
{
uint8_t v___y_15638__boxed_1693_; uint8_t v_suppressElabErrors_boxed_1694_; uint8_t v_res_1695_; lean_object* v_r_1696_; 
v___y_15638__boxed_1693_ = lean_unbox(v___y_1690_);
v_suppressElabErrors_boxed_1694_ = lean_unbox(v_suppressElabErrors_1691_);
v_res_1695_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0(v___y_15638__boxed_1693_, v_suppressElabErrors_boxed_1694_, v_x_1692_);
lean_dec(v_x_1692_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(lean_object* v_ref_1697_, lean_object* v_msgData_1698_, uint8_t v_severity_1699_, uint8_t v_isSilent_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1743_; uint8_t v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1747_; uint8_t v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1779_; lean_object* v___y_1780_; uint8_t v___y_1781_; lean_object* v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; uint8_t v___y_1785_; uint8_t v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; uint8_t v___y_1796_; uint8_t v___y_1797_; uint8_t v___y_1798_; uint8_t v___y_1800_; uint8_t v___x_1815_; 
v___x_1790_ = 2;
v___x_1815_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1699_, v___x_1790_);
if (v___x_1815_ == 0)
{
v___y_1800_ = v___x_1815_;
goto v___jp_1799_;
}
else
{
uint8_t v___x_1816_; 
lean_inc_ref(v_msgData_1698_);
v___x_1816_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1698_);
v___y_1800_ = v___x_1816_;
goto v___jp_1799_;
}
v___jp_1706_:
{
lean_object* v___x_1716_; lean_object* v_currNamespace_1717_; lean_object* v_openDecls_1718_; lean_object* v_env_1719_; lean_object* v_nextMacroScope_1720_; lean_object* v_ngen_1721_; lean_object* v_auxDeclNGen_1722_; lean_object* v_traceState_1723_; lean_object* v_cache_1724_; lean_object* v_messages_1725_; lean_object* v_infoState_1726_; lean_object* v_snapshotTasks_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1741_; 
v___x_1716_ = lean_st_ref_take(v___y_1715_);
v_currNamespace_1717_ = lean_ctor_get(v___y_1714_, 6);
v_openDecls_1718_ = lean_ctor_get(v___y_1714_, 7);
v_env_1719_ = lean_ctor_get(v___x_1716_, 0);
v_nextMacroScope_1720_ = lean_ctor_get(v___x_1716_, 1);
v_ngen_1721_ = lean_ctor_get(v___x_1716_, 2);
v_auxDeclNGen_1722_ = lean_ctor_get(v___x_1716_, 3);
v_traceState_1723_ = lean_ctor_get(v___x_1716_, 4);
v_cache_1724_ = lean_ctor_get(v___x_1716_, 5);
v_messages_1725_ = lean_ctor_get(v___x_1716_, 6);
v_infoState_1726_ = lean_ctor_get(v___x_1716_, 7);
v_snapshotTasks_1727_ = lean_ctor_get(v___x_1716_, 8);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1729_ = v___x_1716_;
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snapshotTasks_1727_);
lean_inc(v_infoState_1726_);
lean_inc(v_messages_1725_);
lean_inc(v_cache_1724_);
lean_inc(v_traceState_1723_);
lean_inc(v_auxDeclNGen_1722_);
lean_inc(v_ngen_1721_);
lean_inc(v_nextMacroScope_1720_);
lean_inc(v_env_1719_);
lean_dec(v___x_1716_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1741_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_inc(v_openDecls_1718_);
lean_inc(v_currNamespace_1717_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_currNamespace_1717_);
lean_ctor_set(v___x_1731_, 1, v_openDecls_1718_);
v___x_1732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v___y_1713_);
lean_inc_ref(v___y_1712_);
lean_inc_ref(v___y_1711_);
v___x_1733_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1733_, 0, v___y_1711_);
lean_ctor_set(v___x_1733_, 1, v___y_1708_);
lean_ctor_set(v___x_1733_, 2, v___y_1709_);
lean_ctor_set(v___x_1733_, 3, v___y_1712_);
lean_ctor_set(v___x_1733_, 4, v___x_1732_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*5, v___y_1710_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*5 + 1, v___y_1707_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*5 + 2, v_isSilent_1700_);
v___x_1734_ = l_Lean_MessageLog_add(v___x_1733_, v_messages_1725_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 6, v___x_1734_);
v___x_1736_ = v___x_1729_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_env_1719_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_nextMacroScope_1720_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_ngen_1721_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_auxDeclNGen_1722_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_traceState_1723_);
lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_cache_1724_);
lean_ctor_set(v_reuseFailAlloc_1740_, 6, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_infoState_1726_);
lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_snapshotTasks_1727_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_st_ref_set(v___y_1715_, v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
v___jp_1742_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1766_; 
v___x_1751_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1698_);
v___x_1752_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v___x_1751_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1766_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1766_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc_ref_n(v___y_1746_, 2);
v___x_1757_ = l_Lean_FileMap_toPosition(v___y_1746_, v___y_1745_);
lean_dec(v___y_1745_);
v___x_1758_ = l_Lean_FileMap_toPosition(v___y_1746_, v___y_1750_);
lean_dec(v___y_1750_);
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1748_ == 0)
{
lean_del_object(v___x_1755_);
lean_dec_ref(v___y_1743_);
v___y_1707_ = v___y_1744_;
v___y_1708_ = v___x_1757_;
v___y_1709_ = v___x_1759_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1749_;
v___y_1712_ = v___x_1760_;
v___y_1713_ = v_a_1753_;
v___y_1714_ = v___y_1703_;
v___y_1715_ = v___y_1704_;
goto v___jp_1706_;
}
else
{
uint8_t v___x_1761_; 
lean_inc(v_a_1753_);
v___x_1761_ = l_Lean_MessageData_hasTag(v___y_1743_, v_a_1753_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec_ref(v___x_1759_);
lean_dec_ref(v___x_1757_);
lean_dec(v_a_1753_);
v___x_1762_ = lean_box(0);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1762_);
v___x_1764_ = v___x_1755_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_del_object(v___x_1755_);
v___y_1707_ = v___y_1744_;
v___y_1708_ = v___x_1757_;
v___y_1709_ = v___x_1759_;
v___y_1710_ = v___y_1747_;
v___y_1711_ = v___y_1749_;
v___y_1712_ = v___x_1760_;
v___y_1713_ = v_a_1753_;
v___y_1714_ = v___y_1703_;
v___y_1715_ = v___y_1704_;
goto v___jp_1706_;
}
}
}
}
v___jp_1767_:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Syntax_getTailPos_x3f(v___y_1770_, v___y_1772_);
lean_dec(v___y_1770_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_inc(v___y_1775_);
v___y_1743_ = v___y_1768_;
v___y_1744_ = v___y_1769_;
v___y_1745_ = v___y_1775_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___y_1773_;
v___y_1750_ = v___y_1775_;
goto v___jp_1742_;
}
else
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref(v___x_1776_);
v___y_1743_ = v___y_1768_;
v___y_1744_ = v___y_1769_;
v___y_1745_ = v___y_1775_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1774_;
v___y_1749_ = v___y_1773_;
v___y_1750_ = v_val_1777_;
goto v___jp_1742_;
}
}
v___jp_1778_:
{
lean_object* v_ref_1786_; lean_object* v___x_1787_; 
v_ref_1786_ = l_Lean_replaceRef(v_ref_1697_, v___y_1782_);
v___x_1787_ = l_Lean_Syntax_getPos_x3f(v_ref_1786_, v___y_1781_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___y_1768_ = v___y_1779_;
v___y_1769_ = v___y_1785_;
v___y_1770_ = v_ref_1786_;
v___y_1771_ = v___y_1780_;
v___y_1772_ = v___y_1781_;
v___y_1773_ = v___y_1784_;
v___y_1774_ = v___y_1783_;
v___y_1775_ = v___x_1788_;
goto v___jp_1767_;
}
else
{
lean_object* v_val_1789_; 
v_val_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v___x_1787_);
v___y_1768_ = v___y_1779_;
v___y_1769_ = v___y_1785_;
v___y_1770_ = v_ref_1786_;
v___y_1771_ = v___y_1780_;
v___y_1772_ = v___y_1781_;
v___y_1773_ = v___y_1784_;
v___y_1774_ = v___y_1783_;
v___y_1775_ = v_val_1789_;
goto v___jp_1767_;
}
}
v___jp_1791_:
{
if (v___y_1798_ == 0)
{
v___y_1779_ = v___y_1793_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1797_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1796_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v_severity_1699_;
goto v___jp_1778_;
}
else
{
v___y_1779_ = v___y_1793_;
v___y_1780_ = v___y_1792_;
v___y_1781_ = v___y_1797_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v___y_1796_;
v___y_1784_ = v___y_1795_;
v___y_1785_ = v___x_1790_;
goto v___jp_1778_;
}
}
v___jp_1799_:
{
if (v___y_1800_ == 0)
{
lean_object* v_fileName_1801_; lean_object* v_fileMap_1802_; lean_object* v_options_1803_; lean_object* v_ref_1804_; uint8_t v_suppressElabErrors_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___f_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; 
v_fileName_1801_ = lean_ctor_get(v___y_1703_, 0);
v_fileMap_1802_ = lean_ctor_get(v___y_1703_, 1);
v_options_1803_ = lean_ctor_get(v___y_1703_, 2);
v_ref_1804_ = lean_ctor_get(v___y_1703_, 5);
v_suppressElabErrors_1805_ = lean_ctor_get_uint8(v___y_1703_, sizeof(void*)*14 + 1);
v___x_1806_ = lean_box(v___y_1800_);
v___x_1807_ = lean_box(v_suppressElabErrors_1805_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1808_, 0, v___x_1806_);
lean_closure_set(v___f_1808_, 1, v___x_1807_);
v___x_1809_ = 1;
v___x_1810_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1699_, v___x_1809_);
if (v___x_1810_ == 0)
{
v___y_1792_ = v_fileMap_1802_;
v___y_1793_ = v___f_1808_;
v___y_1794_ = v_ref_1804_;
v___y_1795_ = v_fileName_1801_;
v___y_1796_ = v_suppressElabErrors_1805_;
v___y_1797_ = v___y_1800_;
v___y_1798_ = v___x_1810_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = l_Lean_warningAsError;
v___x_1812_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_1803_, v___x_1811_);
v___y_1792_ = v_fileMap_1802_;
v___y_1793_ = v___f_1808_;
v___y_1794_ = v_ref_1804_;
v___y_1795_ = v_fileName_1801_;
v___y_1796_ = v_suppressElabErrors_1805_;
v___y_1797_ = v___y_1800_;
v___y_1798_ = v___x_1812_;
goto v___jp_1791_;
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref(v_msgData_1698_);
v___x_1813_ = lean_box(0);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg___boxed(lean_object* v_ref_1817_, lean_object* v_msgData_1818_, lean_object* v_severity_1819_, lean_object* v_isSilent_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
uint8_t v_severity_boxed_1826_; uint8_t v_isSilent_boxed_1827_; lean_object* v_res_1828_; 
v_severity_boxed_1826_ = lean_unbox(v_severity_1819_);
v_isSilent_boxed_1827_ = lean_unbox(v_isSilent_1820_);
v_res_1828_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1817_, v_msgData_1818_, v_severity_boxed_1826_, v_isSilent_boxed_1827_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v_ref_1817_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(lean_object* v_as_1829_, size_t v_sz_1830_, size_t v_i_1831_, lean_object* v_b_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_lt(v_i_1831_, v_sz_1830_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1832_);
return v___x_1841_;
}
else
{
lean_object* v_ref_1842_; lean_object* v_a_1843_; uint8_t v_severity_1844_; lean_object* v_data_1845_; uint8_t v___x_1846_; lean_object* v___x_1847_; 
v_ref_1842_ = lean_ctor_get(v___y_1837_, 5);
v_a_1843_ = lean_array_uget_borrowed(v_as_1829_, v_i_1831_);
v_severity_1844_ = lean_ctor_get_uint8(v_a_1843_, sizeof(void*)*5 + 1);
v_data_1845_ = lean_ctor_get(v_a_1843_, 4);
v___x_1846_ = 0;
lean_inc(v_data_1845_);
v___x_1847_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1842_, v_data_1845_, v_severity_1844_, v___x_1846_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; 
lean_dec_ref(v___x_1847_);
v___x_1848_ = lean_box(0);
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1831_, v___x_1849_);
v_i_1831_ = v___x_1850_;
v_b_1832_ = v___x_1848_;
goto _start;
}
else
{
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4___boxed(lean_object* v_as_1852_, lean_object* v_sz_1853_, lean_object* v_i_1854_, lean_object* v_b_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1853_);
lean_dec(v_sz_1853_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1854_);
lean_dec(v_i_1854_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v_as_1852_, v_sz_boxed_1863_, v_i_boxed_1864_, v_b_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec_ref(v_as_1852_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(uint8_t v_flag_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_infoState_1870_; lean_object* v_env_1871_; lean_object* v_nextMacroScope_1872_; lean_object* v_ngen_1873_; lean_object* v_auxDeclNGen_1874_; lean_object* v_traceState_1875_; lean_object* v_cache_1876_; lean_object* v_messages_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1898_; 
v___x_1869_ = lean_st_ref_take(v___y_1867_);
v_infoState_1870_ = lean_ctor_get(v___x_1869_, 7);
v_env_1871_ = lean_ctor_get(v___x_1869_, 0);
v_nextMacroScope_1872_ = lean_ctor_get(v___x_1869_, 1);
v_ngen_1873_ = lean_ctor_get(v___x_1869_, 2);
v_auxDeclNGen_1874_ = lean_ctor_get(v___x_1869_, 3);
v_traceState_1875_ = lean_ctor_get(v___x_1869_, 4);
v_cache_1876_ = lean_ctor_get(v___x_1869_, 5);
v_messages_1877_ = lean_ctor_get(v___x_1869_, 6);
v_snapshotTasks_1878_ = lean_ctor_get(v___x_1869_, 8);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1880_ = v___x_1869_;
v_isShared_1881_ = v_isSharedCheck_1898_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snapshotTasks_1878_);
lean_inc(v_infoState_1870_);
lean_inc(v_messages_1877_);
lean_inc(v_cache_1876_);
lean_inc(v_traceState_1875_);
lean_inc(v_auxDeclNGen_1874_);
lean_inc(v_ngen_1873_);
lean_inc(v_nextMacroScope_1872_);
lean_inc(v_env_1871_);
lean_dec(v___x_1869_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1898_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_assignment_1882_; lean_object* v_lazyAssignment_1883_; lean_object* v_trees_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1897_; 
v_assignment_1882_ = lean_ctor_get(v_infoState_1870_, 0);
v_lazyAssignment_1883_ = lean_ctor_get(v_infoState_1870_, 1);
v_trees_1884_ = lean_ctor_get(v_infoState_1870_, 2);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_infoState_1870_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1886_ = v_infoState_1870_;
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_trees_1884_);
lean_inc(v_lazyAssignment_1883_);
lean_inc(v_assignment_1882_);
lean_dec(v_infoState_1870_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1897_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_assignment_1882_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_lazyAssignment_1883_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_trees_1884_);
v___x_1889_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*3, v_flag_1866_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 7, v___x_1889_);
v___x_1891_ = v___x_1880_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_env_1871_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_nextMacroScope_1872_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_ngen_1873_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_auxDeclNGen_1874_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_traceState_1875_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_cache_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_messages_1877_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_snapshotTasks_1878_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_set(v___y_1867_, v___x_1891_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg___boxed(lean_object* v_flag_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
uint8_t v_flag_boxed_1902_; lean_object* v_res_1903_; 
v_flag_boxed_1902_ = lean_unbox(v_flag_1899_);
v_res_1903_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_boxed_1902_, v___y_1900_);
lean_dec(v___y_1900_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(uint8_t v_flag_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v_infoState_1914_; uint8_t v_enabled_1915_; lean_object* v_a_1917_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1913_ = lean_st_ref_get(v___y_1911_);
v_infoState_1914_ = lean_ctor_get(v___x_1913_, 7);
lean_inc_ref(v_infoState_1914_);
lean_dec(v___x_1913_);
v_enabled_1915_ = lean_ctor_get_uint8(v_infoState_1914_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1914_);
v___x_1927_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_1904_, v___y_1911_);
lean_dec_ref(v___x_1927_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
v___x_1928_ = lean_apply_7(v_x_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1928_);
v___x_1930_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1915_, v___y_1911_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1930_, 0);
lean_dec(v_unused_1938_);
v___x_1932_ = v___x_1930_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_dec(v___x_1930_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1929_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1929_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1939_; 
v_a_1939_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1928_);
v_a_1917_ = v_a_1939_;
goto v___jp_1916_;
}
v___jp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v___x_1918_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_enabled_1915_, v___y_1911_);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1926_);
v___x_1920_ = v___x_1918_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v___x_1918_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
lean_ctor_set(v___x_1920_, 0, v_a_1917_);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1917_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg___boxed(lean_object* v_flag_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v_flag_boxed_1949_; lean_object* v_res_1950_; 
v_flag_boxed_1949_ = lean_unbox(v_flag_1940_);
v_res_1950_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_boxed_1949_, v_x_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(lean_object* v_msgData_1951_, uint8_t v_severity_1952_, uint8_t v_isSilent_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_ref_1961_; lean_object* v___x_1962_; 
v_ref_1961_ = lean_ctor_get(v___y_1958_, 5);
v___x_1962_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_1961_, v_msgData_1951_, v_severity_1952_, v_isSilent_1953_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0___boxed(lean_object* v_msgData_1963_, lean_object* v_severity_1964_, lean_object* v_isSilent_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v_severity_boxed_1973_; uint8_t v_isSilent_boxed_1974_; lean_object* v_res_1975_; 
v_severity_boxed_1973_ = lean_unbox(v_severity_1964_);
v_isSilent_boxed_1974_ = lean_unbox(v_isSilent_1965_);
v_res_1975_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1963_, v_severity_boxed_1973_, v_isSilent_boxed_1974_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(lean_object* v_msgData_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
uint8_t v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = 2;
v___x_1985_ = 0;
v___x_1986_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringFromString_spec__0_spec__0(v_msgData_1976_, v___x_1984_, v___x_1985_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0___boxed(lean_object* v_msgData_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v_msgData_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(lean_object* v_as_1996_, size_t v_sz_1997_, size_t v_i_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_1998_, v_sz_1997_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v_b_1999_);
return v___x_2008_;
}
else
{
lean_object* v_a_2009_; lean_object* v_snd_2010_; lean_object* v_snd_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2009_ = lean_array_uget_borrowed(v_as_1996_, v_i_1998_);
v_snd_2010_ = lean_ctor_get(v_a_2009_, 1);
v_snd_2011_ = lean_ctor_get(v_snd_2010_, 1);
lean_inc(v_snd_2011_);
v___x_2012_ = l_Lean_Parser_Error_toString(v_snd_2011_);
v___x_2013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
v___x_2014_ = l_Lean_MessageData_ofFormat(v___x_2013_);
v___x_2015_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2014_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; size_t v___x_2017_; size_t v___x_2018_; 
lean_dec_ref(v___x_2015_);
v___x_2016_ = lean_box(0);
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_1998_, v___x_2017_);
v_i_1998_ = v___x_2018_;
v_b_1999_ = v___x_2016_;
goto _start;
}
else
{
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1___boxed(lean_object* v_as_2020_, lean_object* v_sz_2021_, lean_object* v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
size_t v_sz_boxed_2031_; size_t v_i_boxed_2032_; lean_object* v_res_2033_; 
v_sz_boxed_2031_ = lean_unbox_usize(v_sz_2021_);
lean_dec(v_sz_2021_);
v_i_boxed_2032_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v_as_2020_, v_sz_boxed_2031_, v_i_boxed_2032_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec_ref(v_as_2020_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2053_, lean_object* v_docComment_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v___x_2062_; lean_object* v_env_2063_; lean_object* v_fileName_2064_; lean_object* v_options_2065_; lean_object* v_currNamespace_2066_; lean_object* v_openDecls_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2062_ = lean_st_ref_get(v_a_2060_);
v_env_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_ref_n(v_env_2063_, 2);
lean_dec(v___x_2062_);
v_fileName_2064_ = lean_ctor_get(v_a_2059_, 0);
v_options_2065_ = lean_ctor_get(v_a_2059_, 2);
v_currNamespace_2066_ = lean_ctor_get(v_a_2059_, 6);
v_openDecls_2067_ = lean_ctor_get(v_a_2059_, 7);
v___x_2068_ = lean_string_utf8_byte_size(v_docComment_2054_);
lean_inc_ref_n(v_docComment_2054_, 2);
v___x_2069_ = l_Lean_FileMap_ofString(v_docComment_2054_);
lean_inc_ref(v___x_2069_);
lean_inc_ref(v_fileName_2064_);
v___x_2070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2070_, 0, v_docComment_2054_);
lean_ctor_set(v___x_2070_, 1, v_fileName_2064_);
lean_ctor_set(v___x_2070_, 2, v___x_2069_);
lean_ctor_set(v___x_2070_, 3, v___x_2068_);
lean_inc(v_openDecls_2067_);
lean_inc(v_currNamespace_2066_);
lean_inc_ref(v_options_2065_);
v___x_2071_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2071_, 0, v_env_2063_);
lean_ctor_set(v___x_2071_, 1, v_options_2065_);
lean_ctor_set(v___x_2071_, 2, v_currNamespace_2066_);
lean_ctor_set(v___x_2071_, 3, v_openDecls_2067_);
v___x_2072_ = l_Lean_Parser_mkParserState(v_docComment_2054_);
lean_dec_ref(v_docComment_2054_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__2));
v___x_2075_ = l_Lean_Parser_getTokenTable(v_env_2063_);
v___x_2076_ = l_Lean_Parser_ParserFn_run(v___x_2074_, v___x_2070_, v___x_2071_, v___x_2075_, v___x_2072_);
lean_inc_ref(v___x_2076_);
v___x_2077_ = l_Lean_Parser_ParserState_allErrors(v___x_2076_);
v___x_2078_ = lean_array_get_size(v___x_2077_);
v___x_2079_ = lean_nat_dec_eq(v___x_2078_, v___x_2073_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; size_t v_sz_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v___x_2069_);
lean_dec(v_declName_2053_);
v___x_2080_ = lean_box(0);
v_sz_2081_ = lean_array_size(v___x_2077_);
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__1(v___x_2077_, v_sz_2081_, v___x_2082_, v___x_2080_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec_ref(v___x_2077_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v___x_2083_, 0);
lean_dec(v_unused_2092_);
v___x_2085_ = v___x_2083_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_dec(v___x_2083_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2083_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2083_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
else
{
lean_object* v___x_2101_; 
lean_dec_ref(v___x_2077_);
v___x_2101_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2060_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v_a_2104_; lean_object* v_stxStack_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; size_t v_sz_2127_; size_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v_stxStack_2122_ = lean_ctor_get(v___x_2076_, 0);
lean_inc_ref(v_stxStack_2122_);
lean_dec_ref(v___x_2076_);
v___x_2123_ = 0;
v___x_2124_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2122_);
lean_dec_ref(v_stxStack_2122_);
v___x_2125_ = l_Lean_Syntax_getArgs(v___x_2124_);
lean_dec(v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__6));
v_sz_2127_ = lean_array_size(v___x_2125_);
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoModDocString_spec__0(v_sz_2127_, v___x_2128_, v___x_2125_);
v___x_2130_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = 1;
v___x_2132_ = lean_box(v___x_2131_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_versoDocStringFromString___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2133_, 0, v___x_2069_);
lean_closure_set(v___f_2133_, 1, v_declName_2053_);
lean_closure_set(v___f_2133_, 2, v___x_2126_);
lean_closure_set(v___f_2133_, 3, v___x_2130_);
lean_closure_set(v___f_2133_, 4, v___x_2132_);
v___x_2134_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v___x_2123_, v___f_2133_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_2060_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = l_Lean_Core_setMessageLog___redArg(v_a_2102_, v_a_2060_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; size_t v_sz_2141_; lean_object* v___x_2142_; 
lean_dec_ref(v___x_2138_);
v___x_2139_ = l_Lean_MessageLog_toArray(v_a_2137_);
lean_dec(v_a_2137_);
v___x_2140_ = lean_box(0);
v_sz_2141_ = lean_array_size(v___x_2139_);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringFromString_spec__4(v___x_2139_, v_sz_2141_, v___x_2128_, v___x_2140_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
lean_dec_ref(v___x_2139_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v___x_2142_, 0);
lean_dec(v_unused_2150_);
v___x_2144_ = v___x_2142_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_dec(v___x_2142_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v_a_2135_);
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2135_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2135_);
v_a_2151_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2142_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2142_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_a_2137_);
lean_dec(v_a_2135_);
v_a_2159_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2138_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2138_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; 
lean_dec(v_a_2135_);
v_a_2167_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2136_);
v_a_2104_ = v_a_2167_;
goto v___jp_2103_;
}
}
else
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2134_);
v_a_2104_ = v_a_2168_;
goto v___jp_2103_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Core_setMessageLog___redArg(v_a_2102_, v_a_2060_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2113_);
v___x_2107_ = v___x_2105_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v___x_2105_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 1);
lean_ctor_set(v___x_2107_, 0, v_a_2104_);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2104_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec_ref(v_a_2104_);
v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2105_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2105_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v___x_2069_);
lean_dec(v_declName_2053_);
v_a_2169_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2101_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2101_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2177_, lean_object* v_docComment_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_versoDocStringFromString(v_declName_2177_, v_docComment_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(uint8_t v_flag_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___redArg(v_flag_2187_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3___boxed(lean_object* v_flag_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v_flag_boxed_2204_; lean_object* v_res_2205_; 
v_flag_boxed_2204_ = lean_unbox(v_flag_2196_);
v_res_2205_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2_spec__3(v_flag_boxed_2204_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(lean_object* v_00_u03b1_2206_, uint8_t v_flag_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___redArg(v_flag_2207_, v_x_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2___boxed(lean_object* v_00_u03b1_2217_, lean_object* v_flag_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
uint8_t v_flag_boxed_2227_; lean_object* v_res_2228_; 
v_flag_boxed_2227_ = lean_unbox(v_flag_2218_);
v_res_2228_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_versoDocStringFromString_spec__2(v_00_u03b1_2217_, v_flag_boxed_2227_, v_x_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(lean_object* v_ref_2229_, lean_object* v_msgData_2230_, uint8_t v_severity_2231_, uint8_t v_isSilent_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2229_, v_msgData_2230_, v_severity_2231_, v_isSilent_2232_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___boxed(lean_object* v_ref_2241_, lean_object* v_msgData_2242_, lean_object* v_severity_2243_, lean_object* v_isSilent_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
uint8_t v_severity_boxed_2252_; uint8_t v_isSilent_boxed_2253_; lean_object* v_res_2254_; 
v_severity_boxed_2252_ = lean_unbox(v_severity_2243_);
v_isSilent_boxed_2253_ = lean_unbox(v_isSilent_2244_);
v_res_2254_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3(v_ref_2241_, v_msgData_2242_, v_severity_boxed_2252_, v_isSilent_boxed_2253_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v_ref_2241_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2255_, lean_object* v_declName_2256_, lean_object* v_env_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_docStringExt;
v___x_2259_ = l_String_removeLeadingSpaces(v_docString_2255_);
v___x_2260_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2258_, v_env_2257_, v_declName_2256_, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2261_, lean_object* v_modifyEnv_2262_, lean_object* v_docString_2263_){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; 
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2264_, 0, v_docString_2263_);
lean_closure_set(v___f_2264_, 1, v_declName_2261_);
v___x_2265_ = lean_apply_1(v_modifyEnv_2262_, v___f_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_docComment_2268_, lean_object* v_toBind_2269_, lean_object* v___f_2270_, lean_object* v_____r_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = l_Lean_getDocStringText___redArg(v_inst_2266_, v_inst_2267_, v_docComment_2268_);
v___x_2273_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2272_, v___f_2270_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_docComment_2279_, lean_object* v_toBind_2280_, lean_object* v___f_2281_, lean_object* v_____r_2282_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = l_Lean_validateDocComment___redArg(v_inst_2274_, v_inst_2275_, v_inst_2276_, v_inst_2277_, v_inst_2278_, v_docComment_2279_);
v___x_2284_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v___x_2283_, v___f_2281_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_docComment_2290_, lean_object* v_toBind_2291_, lean_object* v___f_2292_, lean_object* v_____r_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2285_, v_inst_2286_, v_inst_2287_, v_inst_2288_, v_inst_2289_, v_docComment_2290_, v_toBind_2291_, v___f_2292_, v_____r_2293_);
lean_dec(v_docComment_2290_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2295_, lean_object* v_____r_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_apply_1(v___f_2295_, v_____r_2296_);
return v___x_2297_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2300_ = l_Lean_stringToMessageData(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2304_, lean_object* v_declName_2305_, uint8_t v___x_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_toBind_2309_, lean_object* v___f_2310_, lean_object* v_____do__lift_2311_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2311_, v_declName_2305_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_dec(v___f_2310_);
lean_dec(v_toBind_2309_);
lean_dec_ref(v_inst_2308_);
lean_dec_ref(v_inst_2307_);
lean_dec(v_declName_2305_);
goto v___jp_2312_;
}
else
{
lean_dec_ref(v___x_2315_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
lean_dec(v___f_2304_);
v___x_2316_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2317_ = l_Lean_MessageData_ofConstName(v_declName_2305_, v___x_2306_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2318_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_throwError___redArg(v_inst_2307_, v_inst_2308_, v___x_2320_);
v___x_2322_ = lean_apply_4(v_toBind_2309_, lean_box(0), lean_box(0), v___x_2321_, v___f_2310_);
return v___x_2322_;
}
else
{
lean_dec(v___f_2310_);
lean_dec(v_toBind_2309_);
lean_dec_ref(v_inst_2308_);
lean_dec_ref(v_inst_2307_);
lean_dec(v_declName_2305_);
goto v___jp_2312_;
}
}
v___jp_2312_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_apply_1(v___f_2304_, v___x_2313_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2323_, lean_object* v_declName_2324_, lean_object* v___x_2325_, lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_toBind_2328_, lean_object* v___f_2329_, lean_object* v_____do__lift_2330_){
_start:
{
uint8_t v___x_389__boxed_2331_; lean_object* v_res_2332_; 
v___x_389__boxed_2331_ = lean_unbox(v___x_2325_);
v_res_2332_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2323_, v_declName_2324_, v___x_389__boxed_2331_, v_inst_2326_, v_inst_2327_, v_toBind_2328_, v___f_2329_, v_____do__lift_2330_);
lean_dec_ref(v_____do__lift_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_declName_2340_, lean_object* v_docComment_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = l_Lean_Name_isAnonymous(v_declName_2340_);
if (v___x_2342_ == 0)
{
lean_object* v_toBind_2343_; lean_object* v_getEnv_2344_; lean_object* v_modifyEnv_2345_; lean_object* v___f_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; 
v_toBind_2343_ = lean_ctor_get(v_inst_2333_, 1);
lean_inc_n(v_toBind_2343_, 4);
v_getEnv_2344_ = lean_ctor_get(v_inst_2336_, 0);
lean_inc(v_getEnv_2344_);
v_modifyEnv_2345_ = lean_ctor_get(v_inst_2336_, 1);
lean_inc(v_modifyEnv_2345_);
lean_dec_ref(v_inst_2336_);
lean_inc(v_declName_2340_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2346_, 0, v_declName_2340_);
lean_closure_set(v___f_2346_, 1, v_modifyEnv_2345_);
lean_inc(v_docComment_2341_);
lean_inc_ref(v_inst_2337_);
lean_inc_ref_n(v_inst_2333_, 2);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2347_, 0, v_inst_2333_);
lean_closure_set(v___f_2347_, 1, v_inst_2337_);
lean_closure_set(v___f_2347_, 2, v_docComment_2341_);
lean_closure_set(v___f_2347_, 3, v_toBind_2343_);
lean_closure_set(v___f_2347_, 4, v___f_2346_);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2348_, 0, v_inst_2333_);
lean_closure_set(v___f_2348_, 1, v_inst_2334_);
lean_closure_set(v___f_2348_, 2, v_inst_2338_);
lean_closure_set(v___f_2348_, 3, v_inst_2339_);
lean_closure_set(v___f_2348_, 4, v_inst_2335_);
lean_closure_set(v___f_2348_, 5, v_docComment_2341_);
lean_closure_set(v___f_2348_, 6, v_toBind_2343_);
lean_closure_set(v___f_2348_, 7, v___f_2347_);
lean_inc_ref(v___f_2348_);
v___f_2349_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2349_, 0, v___f_2348_);
v___x_2350_ = lean_box(v___x_2342_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2351_, 0, v___f_2348_);
lean_closure_set(v___f_2351_, 1, v_declName_2340_);
lean_closure_set(v___f_2351_, 2, v___x_2350_);
lean_closure_set(v___f_2351_, 3, v_inst_2333_);
lean_closure_set(v___f_2351_, 4, v_inst_2337_);
lean_closure_set(v___f_2351_, 5, v_toBind_2343_);
lean_closure_set(v___f_2351_, 6, v___f_2349_);
v___x_2352_ = lean_apply_4(v_toBind_2343_, lean_box(0), lean_box(0), v_getEnv_2344_, v___f_2351_);
return v___x_2352_;
}
else
{
lean_object* v_toApplicative_2353_; lean_object* v_toPure_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_docComment_2341_);
lean_dec(v_declName_2340_);
lean_dec(v_inst_2339_);
lean_dec_ref(v_inst_2338_);
lean_dec_ref(v_inst_2337_);
lean_dec_ref(v_inst_2336_);
lean_dec(v_inst_2335_);
lean_dec(v_inst_2334_);
v_toApplicative_2353_ = lean_ctor_get(v_inst_2333_, 0);
lean_inc_ref(v_toApplicative_2353_);
lean_dec_ref(v_inst_2333_);
v_toPure_2354_ = lean_ctor_get(v_toApplicative_2353_, 1);
lean_inc(v_toPure_2354_);
lean_dec_ref(v_toApplicative_2353_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2355_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_declName_2365_, lean_object* v_docComment_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_addMarkdownDocString___redArg(v_inst_2358_, v_inst_2359_, v_inst_2360_, v_inst_2361_, v_inst_2362_, v_inst_2363_, v_inst_2364_, v_declName_2365_, v_docComment_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2368_, lean_object* v_docs_2369_, lean_object* v_env_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = l_Lean_versoDocStringExt;
v___x_2372_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2371_, v_env_2370_, v_declName_2368_, v_docs_2369_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_modifyEnv_2373_, lean_object* v___f_2374_, lean_object* v_____r_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_apply_1(v_modifyEnv_2373_, v___f_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_2379_, lean_object* v_modifyEnv_2380_, lean_object* v___f_2381_, uint8_t v___x_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_toBind_2385_, lean_object* v___f_2386_, lean_object* v_____do__lift_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2387_, v_declName_2379_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2389_; 
lean_dec(v___f_2386_);
lean_dec(v_toBind_2385_);
lean_dec_ref(v_inst_2384_);
lean_dec_ref(v_inst_2383_);
lean_dec(v_declName_2379_);
v___x_2389_ = lean_apply_1(v_modifyEnv_2380_, v___f_2381_);
return v___x_2389_;
}
else
{
lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2406_; 
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2388_, 0);
lean_dec(v_unused_2407_);
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2406_;
goto v_resetjp_2390_;
}
else
{
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2406_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
if (v___x_2382_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
lean_dec_ref(v___f_2381_);
lean_dec(v_modifyEnv_2380_);
v___x_2393_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2394_ = 1;
v___x_2395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2379_, v___x_2394_);
v___x_2396_ = lean_string_append(v___x_2393_, v___x_2395_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 3);
lean_ctor_set(v___x_2391_, 0, v___x_2398_);
v___x_2400_ = v___x_2391_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = l_Lean_MessageData_ofFormat(v___x_2400_);
v___x_2402_ = l_Lean_throwError___redArg(v_inst_2383_, v_inst_2384_, v___x_2401_);
v___x_2403_ = lean_apply_4(v_toBind_2385_, lean_box(0), lean_box(0), v___x_2402_, v___f_2386_);
return v___x_2403_;
}
}
else
{
lean_object* v___x_2405_; 
lean_del_object(v___x_2391_);
lean_dec(v___f_2386_);
lean_dec(v_toBind_2385_);
lean_dec_ref(v_inst_2384_);
lean_dec_ref(v_inst_2383_);
lean_dec(v_declName_2379_);
v___x_2405_ = lean_apply_1(v_modifyEnv_2380_, v___f_2381_);
return v___x_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_2408_, lean_object* v_modifyEnv_2409_, lean_object* v___f_2410_, lean_object* v___x_2411_, lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_toBind_2414_, lean_object* v___f_2415_, lean_object* v_____do__lift_2416_){
_start:
{
uint8_t v___x_303__boxed_2417_; lean_object* v_res_2418_; 
v___x_303__boxed_2417_ = lean_unbox(v___x_2411_);
v_res_2418_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_2408_, v_modifyEnv_2409_, v___f_2410_, v___x_303__boxed_2417_, v_inst_2412_, v_inst_2413_, v_toBind_2414_, v___f_2415_, v_____do__lift_2416_);
lean_dec_ref(v_____do__lift_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_declName_2422_, lean_object* v_docs_2423_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = l_Lean_Name_isAnonymous(v_declName_2422_);
if (v___x_2424_ == 0)
{
lean_object* v_toBind_2425_; lean_object* v_getEnv_2426_; lean_object* v_modifyEnv_2427_; lean_object* v___f_2428_; lean_object* v___f_2429_; lean_object* v___x_2430_; lean_object* v___f_2431_; lean_object* v___x_2432_; 
v_toBind_2425_ = lean_ctor_get(v_inst_2419_, 1);
lean_inc_n(v_toBind_2425_, 2);
v_getEnv_2426_ = lean_ctor_get(v_inst_2420_, 0);
lean_inc(v_getEnv_2426_);
v_modifyEnv_2427_ = lean_ctor_get(v_inst_2420_, 1);
lean_inc_n(v_modifyEnv_2427_, 2);
lean_dec_ref(v_inst_2420_);
lean_inc(v_declName_2422_);
v___f_2428_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2428_, 0, v_declName_2422_);
lean_closure_set(v___f_2428_, 1, v_docs_2423_);
lean_inc_ref(v___f_2428_);
v___f_2429_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2429_, 0, v_modifyEnv_2427_);
lean_closure_set(v___f_2429_, 1, v___f_2428_);
v___x_2430_ = lean_box(v___x_2424_);
v___f_2431_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2431_, 0, v_declName_2422_);
lean_closure_set(v___f_2431_, 1, v_modifyEnv_2427_);
lean_closure_set(v___f_2431_, 2, v___f_2428_);
lean_closure_set(v___f_2431_, 3, v___x_2430_);
lean_closure_set(v___f_2431_, 4, v_inst_2419_);
lean_closure_set(v___f_2431_, 5, v_inst_2421_);
lean_closure_set(v___f_2431_, 6, v_toBind_2425_);
lean_closure_set(v___f_2431_, 7, v___f_2429_);
v___x_2432_ = lean_apply_4(v_toBind_2425_, lean_box(0), lean_box(0), v_getEnv_2426_, v___f_2431_);
return v___x_2432_;
}
else
{
lean_object* v_toApplicative_2433_; lean_object* v_toPure_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_dec_ref(v_docs_2423_);
lean_dec(v_declName_2422_);
lean_dec_ref(v_inst_2421_);
lean_dec_ref(v_inst_2420_);
v_toApplicative_2433_ = lean_ctor_get(v_inst_2419_, 0);
lean_inc_ref(v_toApplicative_2433_);
lean_dec_ref(v_inst_2419_);
v_toPure_2434_ = lean_ctor_get(v_toApplicative_2433_, 1);
lean_inc(v_toPure_2434_);
lean_dec_ref(v_toApplicative_2433_);
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_apply_2(v_toPure_2434_, lean_box(0), v___x_2435_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_declName_2442_, lean_object* v_docs_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2438_, v_inst_2439_, v_inst_2441_, v_declName_2442_, v_docs_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_declName_2450_, lean_object* v_docs_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_addVersoDocStringCore(v_m_2445_, v_inst_2446_, v_inst_2447_, v_inst_2448_, v_inst_2449_, v_declName_2450_, v_docs_2451_);
lean_dec(v_inst_2448_);
return v_res_2452_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_____do__lift_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2460_, v_docs_2456_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec_ref(v_inst_2459_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref(v___x_2461_);
v___x_2463_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_2464_ = l_Lean_stringToMessageData(v_a_2462_);
v___x_2465_ = l_Lean_indentD(v___x_2464_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = l_Lean_throwError___redArg(v_inst_2457_, v_inst_2458_, v___x_2466_);
return v___x_2467_;
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
lean_dec_ref(v_inst_2458_);
lean_dec_ref(v_inst_2457_);
v_a_2468_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2461_);
v___x_2469_ = l_Lean_setEnv___redArg(v_inst_2459_, v_a_2468_);
return v___x_2469_;
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_toBind_2475_, lean_object* v_getEnv_2476_, lean_object* v___f_2477_, lean_object* v_____do__lift_2478_){
_start:
{
lean_object* v___x_2479_; uint8_t v___x_2480_; 
v___x_2479_ = l_Lean_getMainModuleDoc(v_____do__lift_2478_);
v___x_2480_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2479_);
lean_dec_ref(v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec(v___f_2477_);
lean_dec(v_getEnv_2476_);
lean_dec(v_toBind_2475_);
v___x_2481_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2482_ = l_Lean_throwError___redArg(v_inst_2473_, v_inst_2474_, v___x_2481_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; 
lean_dec_ref(v_inst_2474_);
lean_dec_ref(v_inst_2473_);
v___x_2483_ = lean_apply_4(v_toBind_2475_, lean_box(0), lean_box(0), v_getEnv_2476_, v___f_2477_);
return v___x_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_docs_2487_){
_start:
{
lean_object* v_toBind_2488_; lean_object* v_getEnv_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
v_toBind_2488_ = lean_ctor_get(v_inst_2484_, 1);
lean_inc_n(v_toBind_2488_, 2);
v_getEnv_2489_ = lean_ctor_get(v_inst_2485_, 0);
lean_inc_n(v_getEnv_2489_, 2);
lean_inc_ref(v_inst_2486_);
lean_inc_ref(v_inst_2484_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2490_, 0, v_docs_2487_);
lean_closure_set(v___f_2490_, 1, v_inst_2484_);
lean_closure_set(v___f_2490_, 2, v_inst_2486_);
lean_closure_set(v___f_2490_, 3, v_inst_2485_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2491_, 0, v_inst_2484_);
lean_closure_set(v___f_2491_, 1, v_inst_2486_);
lean_closure_set(v___f_2491_, 2, v_toBind_2488_);
lean_closure_set(v___f_2491_, 3, v_getEnv_2489_);
lean_closure_set(v___f_2491_, 4, v___f_2490_);
v___x_2492_ = lean_apply_4(v_toBind_2488_, lean_box(0), lean_box(0), v_getEnv_2489_, v___f_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_docs_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2494_, v_inst_2495_, v_inst_2497_, v_docs_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_docs_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_addVersoModDocStringCore(v_m_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_inst_2504_, v_docs_2505_);
lean_dec(v_inst_2503_);
return v_res_2506_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
return v___x_2511_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2513_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
lean_ctor_set(v___x_2513_, 2, v___x_2512_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
lean_ctor_set(v___x_2513_, 4, v___x_2512_);
lean_ctor_set(v___x_2513_, 5, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2514_, lean_object* v_docs_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___y_2524_; lean_object* v___y_2525_; uint8_t v___x_2564_; 
v___x_2564_ = l_Lean_Name_isAnonymous(v_declName_2514_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v_env_2566_; lean_object* v___x_2567_; 
v___x_2565_ = lean_st_ref_get(v___y_2521_);
v_env_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc_ref(v_env_2566_);
lean_dec(v___x_2565_);
v___x_2567_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2566_, v_declName_2514_);
lean_dec_ref(v_env_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
v___y_2524_ = v___y_2519_;
v___y_2525_ = v___y_2521_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2582_; 
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2583_);
v___x_2569_ = v___x_2567_;
v_isShared_2570_ = v_isSharedCheck_2582_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2567_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2582_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
if (v___x_2564_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_dec_ref(v_docs_2515_);
v___x_2571_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2572_ = 1;
v___x_2573_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2514_, v___x_2572_);
v___x_2574_ = lean_string_append(v___x_2571_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
if (v_isShared_2570_ == 0)
{
lean_ctor_set_tag(v___x_2569_, 3);
lean_ctor_set(v___x_2569_, 0, v___x_2576_);
v___x_2578_ = v___x_2569_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = l_Lean_MessageData_ofFormat(v___x_2578_);
v___x_2580_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2579_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2580_;
}
}
else
{
lean_del_object(v___x_2569_);
v___y_2524_ = v___y_2519_;
v___y_2525_ = v___y_2521_;
goto v___jp_2523_;
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_dec_ref(v_docs_2515_);
lean_dec(v_declName_2514_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
return v___x_2585_;
}
v___jp_2523_:
{
lean_object* v___x_2526_; lean_object* v_env_2527_; lean_object* v_nextMacroScope_2528_; lean_object* v_ngen_2529_; lean_object* v_auxDeclNGen_2530_; lean_object* v_traceState_2531_; lean_object* v_messages_2532_; lean_object* v_infoState_2533_; lean_object* v_snapshotTasks_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2562_; 
v___x_2526_ = lean_st_ref_take(v___y_2525_);
v_env_2527_ = lean_ctor_get(v___x_2526_, 0);
v_nextMacroScope_2528_ = lean_ctor_get(v___x_2526_, 1);
v_ngen_2529_ = lean_ctor_get(v___x_2526_, 2);
v_auxDeclNGen_2530_ = lean_ctor_get(v___x_2526_, 3);
v_traceState_2531_ = lean_ctor_get(v___x_2526_, 4);
v_messages_2532_ = lean_ctor_get(v___x_2526_, 6);
v_infoState_2533_ = lean_ctor_get(v___x_2526_, 7);
v_snapshotTasks_2534_ = lean_ctor_get(v___x_2526_, 8);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2526_, 5);
lean_dec(v_unused_2563_);
v___x_2536_ = v___x_2526_;
v_isShared_2537_ = v_isSharedCheck_2562_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snapshotTasks_2534_);
lean_inc(v_infoState_2533_);
lean_inc(v_messages_2532_);
lean_inc(v_traceState_2531_);
lean_inc(v_auxDeclNGen_2530_);
lean_inc(v_ngen_2529_);
lean_inc(v_nextMacroScope_2528_);
lean_inc(v_env_2527_);
lean_dec(v___x_2526_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2562_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
v___x_2538_ = l_Lean_versoDocStringExt;
v___x_2539_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2538_, v_env_2527_, v_declName_2514_, v_docs_2515_);
v___x_2540_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 5, v___x_2540_);
lean_ctor_set(v___x_2536_, 0, v___x_2539_);
v___x_2542_ = v___x_2536_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_nextMacroScope_2528_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_ngen_2529_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_auxDeclNGen_2530_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_traceState_2531_);
lean_ctor_set(v_reuseFailAlloc_2561_, 5, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2561_, 6, v_messages_2532_);
lean_ctor_set(v_reuseFailAlloc_2561_, 7, v_infoState_2533_);
lean_ctor_set(v_reuseFailAlloc_2561_, 8, v_snapshotTasks_2534_);
v___x_2542_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_mctx_2545_; lean_object* v_zetaDeltaFVarIds_2546_; lean_object* v_postponed_2547_; lean_object* v_diag_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2559_; 
v___x_2543_ = lean_st_ref_set(v___y_2525_, v___x_2542_);
v___x_2544_ = lean_st_ref_take(v___y_2524_);
v_mctx_2545_ = lean_ctor_get(v___x_2544_, 0);
v_zetaDeltaFVarIds_2546_ = lean_ctor_get(v___x_2544_, 2);
v_postponed_2547_ = lean_ctor_get(v___x_2544_, 3);
v_diag_2548_ = lean_ctor_get(v___x_2544_, 4);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2544_, 1);
lean_dec(v_unused_2560_);
v___x_2550_ = v___x_2544_;
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_diag_2548_);
lean_inc(v_postponed_2547_);
lean_inc(v_zetaDeltaFVarIds_2546_);
lean_inc(v_mctx_2545_);
lean_dec(v___x_2544_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2559_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
v___x_2552_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2552_);
v___x_2554_ = v___x_2550_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_mctx_2545_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_zetaDeltaFVarIds_2546_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v_postponed_2547_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_diag_2548_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = lean_st_ref_set(v___y_2524_, v___x_2554_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
return v___x_2557_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2586_, lean_object* v_docs_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2586_, v_docs_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2596_, lean_object* v_binders_2597_, lean_object* v_docComment_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___x_2633_; lean_object* v_env_2634_; lean_object* v___x_2635_; 
v___x_2633_ = lean_st_ref_get(v_a_2604_);
v_env_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc_ref(v_env_2634_);
lean_dec(v___x_2633_);
v___x_2635_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2634_, v_declName_2596_);
lean_dec_ref(v_env_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
v___y_2607_ = v_a_2599_;
v___y_2608_ = v_a_2600_;
v___y_2609_ = v_a_2601_;
v___y_2610_ = v_a_2602_;
v___y_2611_ = v_a_2603_;
v___y_2612_ = v_a_2604_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_docComment_2598_);
lean_dec(v_binders_2597_);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v___x_2635_, 0);
lean_dec(v_unused_2651_);
v___x_2637_ = v___x_2635_;
v_isShared_2638_ = v_isSharedCheck_2650_;
goto v_resetjp_2636_;
}
else
{
lean_dec(v___x_2635_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2650_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2639_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2640_ = 1;
v___x_2641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2596_, v___x_2640_);
v___x_2642_ = lean_string_append(v___x_2639_, v___x_2641_);
lean_dec_ref(v___x_2641_);
v___x_2643_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2644_ = lean_string_append(v___x_2642_, v___x_2643_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set_tag(v___x_2637_, 3);
lean_ctor_set(v___x_2637_, 0, v___x_2644_);
v___x_2646_ = v___x_2637_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = l_Lean_MessageData_ofFormat(v___x_2646_);
v___x_2648_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2647_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
return v___x_2648_;
}
}
}
v___jp_2606_:
{
lean_object* v___x_2613_; 
lean_inc(v_declName_2596_);
v___x_2613_ = l_Lean_versoDocString(v_declName_2596_, v_binders_2597_, v_docComment_2598_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2624_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2613_);
v_fst_2615_ = lean_ctor_get(v_a_2614_, 0);
v_snd_2616_ = lean_ctor_get(v_a_2614_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_a_2614_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2618_ = v_a_2614_;
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_inc(v_fst_2615_);
lean_dec(v_a_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_fst_2615_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_snd_2616_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2596_, v___x_2621_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_declName_2596_);
v_a_2625_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2613_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2613_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2652_, lean_object* v_binders_2653_, lean_object* v_docComment_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_addVersoDocString(v_declName_2652_, v_binders_2653_, v_docComment_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2663_, lean_object* v_docComment_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___x_2699_; lean_object* v_env_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_st_ref_get(v_a_2670_);
v_env_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_ref(v_env_2700_);
lean_dec(v___x_2699_);
v___x_2701_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2700_, v_declName_2663_);
lean_dec_ref(v_env_2700_);
if (lean_obj_tag(v___x_2701_) == 0)
{
v___y_2673_ = v_a_2665_;
v___y_2674_ = v_a_2666_;
v___y_2675_ = v_a_2667_;
v___y_2676_ = v_a_2668_;
v___y_2677_ = v_a_2669_;
v___y_2678_ = v_a_2670_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v_docComment_2664_);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v___x_2701_, 0);
lean_dec(v_unused_2717_);
v___x_2703_ = v___x_2701_;
v_isShared_2704_ = v_isSharedCheck_2716_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v___x_2701_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2716_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2705_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0));
v___x_2706_ = 1;
v___x_2707_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2663_, v___x_2706_);
v___x_2708_ = lean_string_append(v___x_2705_, v___x_2707_);
lean_dec_ref(v___x_2707_);
v___x_2709_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1));
v___x_2710_ = lean_string_append(v___x_2708_, v___x_2709_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set_tag(v___x_2703_, 3);
lean_ctor_set(v___x_2703_, 0, v___x_2710_);
v___x_2712_ = v___x_2703_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = l_Lean_MessageData_ofFormat(v___x_2712_);
v___x_2714_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2713_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2714_;
}
}
}
v___jp_2672_:
{
lean_object* v___x_2679_; 
lean_inc(v_declName_2663_);
v___x_2679_ = l_Lean_versoDocStringFromString(v_declName_2663_, v_docComment_2664_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_fst_2681_; lean_object* v_snd_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2690_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
v_fst_2681_ = lean_ctor_get(v_a_2680_, 0);
v_snd_2682_ = lean_ctor_get(v_a_2680_, 1);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_a_2680_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2684_ = v_a_2680_;
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_snd_2682_);
lean_inc(v_fst_2681_);
lean_dec(v_a_2680_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2690_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_fst_2681_);
lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_snd_2682_);
v___x_2687_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2663_, v___x_2687_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2688_;
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_declName_2663_);
v_a_2691_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2679_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2679_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2718_, lean_object* v_docComment_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_addVersoDocStringFromString(v_declName_2718_, v_docComment_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2728_, lean_object* v_msgData_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v___x_2735_; uint8_t v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = 2;
v___x_2736_ = 0;
v___x_2737_ = l_Lean_logAt___at___00Lean_versoDocStringFromString_spec__3___redArg(v_ref_2728_, v_msgData_2729_, v___x_2735_, v___x_2736_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2738_, lean_object* v_msgData_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2738_, v_msgData_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v_ref_2738_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2746_, lean_object* v_str_2747_, lean_object* v_as_2748_, size_t v_sz_2749_, size_t v_i_2750_, lean_object* v_b_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_a_2760_; uint8_t v___x_2764_; 
v___x_2764_ = lean_usize_dec_lt(v_i_2750_, v_sz_2749_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_b_2751_);
return v___x_2765_;
}
else
{
lean_object* v_a_2766_; lean_object* v_fst_2767_; lean_object* v_snd_2768_; lean_object* v_start_2769_; lean_object* v_stop_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2790_; 
v_a_2766_ = lean_array_uget_borrowed(v_as_2748_, v_i_2750_);
v_fst_2767_ = lean_ctor_get(v_a_2766_, 0);
lean_inc(v_fst_2767_);
v_snd_2768_ = lean_ctor_get(v_a_2766_, 1);
v_start_2769_ = lean_ctor_get(v_fst_2767_, 0);
v_stop_2770_ = lean_ctor_get(v_fst_2767_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_fst_2767_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2772_ = v_fst_2767_;
v_isShared_2773_ = v_isSharedCheck_2790_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_stop_2770_);
lean_inc(v_start_2769_);
lean_dec(v_fst_2767_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2790_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; 
v___x_2774_ = lean_box(0);
if (lean_obj_tag(v___y_2746_) == 1)
{
lean_object* v_val_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v_val_2775_ = lean_ctor_get(v___y_2746_, 0);
v___x_2776_ = lean_nat_add(v_val_2775_, v_start_2769_);
v___x_2777_ = lean_nat_add(v_val_2775_, v_stop_2770_);
v___x_2778_ = 0;
v___x_2779_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2779_, 0, v___x_2776_);
lean_ctor_set(v___x_2779_, 1, v___x_2777_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*2, v___x_2778_);
v___x_2780_ = lean_string_utf8_extract(v_str_2747_, v_start_2769_, v_stop_2770_);
lean_dec(v_stop_2770_);
lean_dec(v_start_2769_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 2);
lean_ctor_set(v___x_2772_, 1, v___x_2780_);
lean_ctor_set(v___x_2772_, 0, v___x_2779_);
v___x_2782_ = v___x_2772_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_inc(v_snd_2768_);
v___x_2783_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_snd_2768_);
v___x_2784_ = l_Lean_MessageData_ofFormat(v___x_2783_);
v___x_2785_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2782_, v___x_2784_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec_ref(v___x_2782_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_dec_ref(v___x_2785_);
v_a_2760_ = v___x_2774_;
goto v___jp_2759_;
}
else
{
return v___x_2785_;
}
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_del_object(v___x_2772_);
lean_dec(v_stop_2770_);
lean_dec(v_start_2769_);
lean_inc(v_snd_2768_);
v___x_2787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_snd_2768_);
v___x_2788_ = l_Lean_MessageData_ofFormat(v___x_2787_);
v___x_2789_ = l_Lean_logError___at___00Lean_versoDocStringFromString_spec__0(v___x_2788_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_dec_ref(v___x_2789_);
v_a_2760_ = v___x_2774_;
goto v___jp_2759_;
}
else
{
return v___x_2789_;
}
}
}
}
v___jp_2759_:
{
size_t v___x_2761_; size_t v___x_2762_; 
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2750_, v___x_2761_);
v_i_2750_ = v___x_2762_;
v_b_2751_ = v_a_2760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2791_, lean_object* v_str_2792_, lean_object* v_as_2793_, lean_object* v_sz_2794_, lean_object* v_i_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
size_t v_sz_boxed_2804_; size_t v_i_boxed_2805_; lean_object* v_res_2806_; 
v_sz_boxed_2804_ = lean_unbox_usize(v_sz_2794_);
lean_dec(v_sz_2794_);
v_i_boxed_2805_ = lean_unbox_usize(v_i_2795_);
lean_dec(v_i_2795_);
v_res_2806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2791_, v_str_2792_, v_as_2793_, v_sz_boxed_2804_, v_i_boxed_2805_, v_b_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec_ref(v_as_2793_);
lean_dec_ref(v_str_2792_);
lean_dec(v___y_2791_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v_str_2815_; lean_object* v___y_2817_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_str_2815_ = l_Lean_TSyntax_getDocString(v_docstring_2807_);
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = l_Lean_Syntax_getArg(v_docstring_2807_, v___x_2832_);
v___x_2834_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2833_);
lean_dec(v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_box(0);
v___y_2817_ = v___x_2835_;
goto v___jp_2816_;
}
else
{
lean_object* v_val_2836_; uint8_t v___x_2837_; lean_object* v___x_2838_; 
v_val_2836_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_val_2836_);
lean_dec_ref(v___x_2834_);
v___x_2837_ = 0;
v___x_2838_ = l_Lean_SourceInfo_getPos_x3f(v_val_2836_, v___x_2837_);
lean_dec(v_val_2836_);
v___y_2817_ = v___x_2838_;
goto v___jp_2816_;
}
v___jp_2816_:
{
lean_object* v___x_2818_; lean_object* v_fst_2819_; lean_object* v___x_2820_; size_t v_sz_2821_; size_t v___x_2822_; lean_object* v___x_2823_; 
lean_inc_ref(v_str_2815_);
v___x_2818_ = l_Lean_rewriteManualLinksCore(v_str_2815_);
v_fst_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_fst_2819_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = lean_box(0);
v_sz_2821_ = lean_array_size(v_fst_2819_);
v___x_2822_ = ((size_t)0ULL);
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2817_, v_str_2815_, v_fst_2819_, v_sz_2821_, v___x_2822_, v___x_2820_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v_fst_2819_);
lean_dec_ref(v_str_2815_);
lean_dec(v___y_2817_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2831_);
v___x_2825_ = v___x_2823_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v___x_2823_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2820_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2820_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
return v___x_2823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v_docstring_2839_);
return v_res_2847_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2850_ = l_Lean_stringToMessageData(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_val_2866_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = l_Lean_Syntax_getArg(v_stx_2851_, v___x_2873_);
switch(lean_obj_tag(v___x_2874_))
{
case 2:
{
lean_object* v_val_2875_; 
lean_dec(v_stx_2851_);
v_val_2875_ = lean_ctor_get(v___x_2874_, 1);
lean_inc_ref(v_val_2875_);
lean_dec_ref(v___x_2874_);
v_val_2866_ = v_val_2875_;
goto v___jp_2865_;
}
case 1:
{
lean_object* v_kind_2876_; 
v_kind_2876_ = lean_ctor_get(v___x_2874_, 1);
lean_inc(v_kind_2876_);
if (lean_obj_tag(v_kind_2876_) == 1)
{
lean_object* v_pre_2877_; 
v_pre_2877_ = lean_ctor_get(v_kind_2876_, 0);
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
lean_inc(v_pre_2879_);
if (lean_obj_tag(v_pre_2879_) == 1)
{
lean_object* v_pre_2880_; 
v_pre_2880_ = lean_ctor_get(v_pre_2879_, 0);
if (lean_obj_tag(v_pre_2880_) == 0)
{
lean_object* v_str_2881_; lean_object* v_str_2882_; lean_object* v_str_2883_; lean_object* v_str_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v_str_2881_ = lean_ctor_get(v_kind_2876_, 1);
lean_inc_ref(v_str_2881_);
lean_dec_ref(v_kind_2876_);
v_str_2882_ = lean_ctor_get(v_pre_2877_, 1);
lean_inc_ref(v_str_2882_);
lean_dec_ref(v_pre_2877_);
v_str_2883_ = lean_ctor_get(v_pre_2878_, 1);
lean_inc_ref(v_str_2883_);
lean_dec_ref(v_pre_2878_);
v_str_2884_ = lean_ctor_get(v_pre_2879_, 1);
lean_inc_ref(v_str_2884_);
lean_dec_ref(v_pre_2879_);
v___x_2885_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2886_ = lean_string_dec_eq(v_str_2884_, v___x_2885_);
lean_dec_ref(v_str_2884_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v_str_2883_);
lean_dec_ref(v_str_2882_);
lean_dec_ref(v_str_2881_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2887_; uint8_t v___x_2888_; 
v___x_2887_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2888_ = lean_string_dec_eq(v_str_2883_, v___x_2887_);
lean_dec_ref(v_str_2883_);
if (v___x_2888_ == 0)
{
lean_dec_ref(v_str_2882_);
lean_dec_ref(v_str_2881_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2889_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2890_ = lean_string_dec_eq(v_str_2882_, v___x_2889_);
lean_dec_ref(v_str_2882_);
if (v___x_2890_ == 0)
{
lean_dec_ref(v_str_2881_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2892_ = lean_string_dec_eq(v_str_2881_, v___x_2891_);
lean_dec_ref(v_str_2881_);
if (v___x_2892_ == 0)
{
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2893_);
lean_dec_ref(v___x_2874_);
if (lean_obj_tag(v___x_2894_) == 2)
{
lean_object* v_val_2895_; 
lean_dec(v_stx_2851_);
v_val_2895_ = lean_ctor_get(v___x_2894_, 1);
lean_inc_ref(v_val_2895_);
lean_dec_ref(v___x_2894_);
v_val_2866_ = v_val_2895_;
goto v___jp_2865_;
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
lean_dec(v___x_2894_);
v___x_2896_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2851_);
v___x_2897_ = l_Lean_MessageData_ofSyntax(v_stx_2851_);
v___x_2898_ = l_Lean_indentD(v___x_2897_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2896_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2851_, v___x_2899_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v_stx_2851_);
return v___x_2900_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_2879_);
lean_dec_ref(v_pre_2878_);
lean_dec_ref(v_pre_2877_);
lean_dec_ref(v_kind_2876_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
}
else
{
lean_dec(v_pre_2879_);
lean_dec_ref(v_pre_2878_);
lean_dec_ref(v_pre_2877_);
lean_dec_ref(v_kind_2876_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
}
else
{
lean_dec_ref(v_pre_2877_);
lean_dec(v_pre_2878_);
lean_dec_ref(v_kind_2876_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
}
else
{
lean_dec_ref(v_kind_2876_);
lean_dec(v_pre_2877_);
lean_dec_ref(v___x_2874_);
goto v___jp_2859_;
}
}
else
{
lean_dec_ref(v___x_2874_);
lean_dec(v_kind_2876_);
goto v___jp_2859_;
}
}
default: 
{
lean_dec(v___x_2874_);
goto v___jp_2859_;
}
}
v___jp_2859_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2860_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2851_);
v___x_2861_ = l_Lean_MessageData_ofSyntax(v_stx_2851_);
v___x_2862_ = l_Lean_indentD(v___x_2861_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2860_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_2851_, v___x_2863_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v_stx_2851_);
return v___x_2864_;
}
v___jp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = lean_string_utf8_byte_size(v_val_2866_);
v___x_2869_ = lean_unsigned_to_nat(2u);
v___x_2870_ = lean_nat_sub(v___x_2868_, v___x_2869_);
v___x_2871_ = lean_string_utf8_extract(v_val_2866_, v___x_2867_, v___x_2870_);
lean_dec(v___x_2870_);
lean_dec_ref(v_val_2866_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2910_, lean_object* v_docComment_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; uint8_t v___x_2982_; 
v___x_2982_ = l_Lean_Name_isAnonymous(v_declName_2910_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_st_ref_get(v___y_2917_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2985_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2984_, v_declName_2910_);
lean_dec_ref(v_env_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
v___y_2920_ = v___y_2912_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
goto v___jp_2919_;
}
else
{
lean_dec_ref(v___x_2985_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v_docComment_2911_);
v___x_2986_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2987_ = l_Lean_MessageData_ofConstName(v_declName_2910_, v___x_2982_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2988_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2990_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2991_;
}
else
{
v___y_2920_ = v___y_2912_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
goto v___jp_2919_;
}
}
}
else
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec(v_docComment_2911_);
lean_dec(v_declName_2910_);
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
return v___x_2993_;
}
v___jp_2919_:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2911_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v___x_2927_; 
lean_dec_ref(v___x_2926_);
v___x_2927_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2911_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2973_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2973_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2973_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v_env_2933_; lean_object* v_nextMacroScope_2934_; lean_object* v_ngen_2935_; lean_object* v_auxDeclNGen_2936_; lean_object* v_traceState_2937_; lean_object* v_messages_2938_; lean_object* v_infoState_2939_; lean_object* v_snapshotTasks_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2971_; 
v___x_2932_ = lean_st_ref_take(v___y_2925_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
v_nextMacroScope_2934_ = lean_ctor_get(v___x_2932_, 1);
v_ngen_2935_ = lean_ctor_get(v___x_2932_, 2);
v_auxDeclNGen_2936_ = lean_ctor_get(v___x_2932_, 3);
v_traceState_2937_ = lean_ctor_get(v___x_2932_, 4);
v_messages_2938_ = lean_ctor_get(v___x_2932_, 6);
v_infoState_2939_ = lean_ctor_get(v___x_2932_, 7);
v_snapshotTasks_2940_ = lean_ctor_get(v___x_2932_, 8);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v___x_2932_, 5);
lean_dec(v_unused_2972_);
v___x_2942_ = v___x_2932_;
v_isShared_2943_ = v_isSharedCheck_2971_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snapshotTasks_2940_);
lean_inc(v_infoState_2939_);
lean_inc(v_messages_2938_);
lean_inc(v_traceState_2937_);
lean_inc(v_auxDeclNGen_2936_);
lean_inc(v_ngen_2935_);
lean_inc(v_nextMacroScope_2934_);
lean_inc(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2971_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2944_ = l_Lean_docStringExt;
v___x_2945_ = l_String_removeLeadingSpaces(v_a_2928_);
v___x_2946_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2944_, v_env_2933_, v_declName_2910_, v___x_2945_);
v___x_2947_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 5, v___x_2947_);
lean_ctor_set(v___x_2942_, 0, v___x_2946_);
v___x_2949_ = v___x_2942_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_nextMacroScope_2934_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_ngen_2935_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_auxDeclNGen_2936_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_traceState_2937_);
lean_ctor_set(v_reuseFailAlloc_2970_, 5, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2970_, 6, v_messages_2938_);
lean_ctor_set(v_reuseFailAlloc_2970_, 7, v_infoState_2939_);
lean_ctor_set(v_reuseFailAlloc_2970_, 8, v_snapshotTasks_2940_);
v___x_2949_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_mctx_2952_; lean_object* v_zetaDeltaFVarIds_2953_; lean_object* v_postponed_2954_; lean_object* v_diag_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2968_; 
v___x_2950_ = lean_st_ref_set(v___y_2925_, v___x_2949_);
v___x_2951_ = lean_st_ref_take(v___y_2923_);
v_mctx_2952_ = lean_ctor_get(v___x_2951_, 0);
v_zetaDeltaFVarIds_2953_ = lean_ctor_get(v___x_2951_, 2);
v_postponed_2954_ = lean_ctor_get(v___x_2951_, 3);
v_diag_2955_ = lean_ctor_get(v___x_2951_, 4);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2951_, 1);
lean_dec(v_unused_2969_);
v___x_2957_ = v___x_2951_;
v_isShared_2958_ = v_isSharedCheck_2968_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_diag_2955_);
lean_inc(v_postponed_2954_);
lean_inc(v_zetaDeltaFVarIds_2953_);
lean_inc(v_mctx_2952_);
lean_dec(v___x_2951_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2968_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2959_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_mctx_2952_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_zetaDeltaFVarIds_2953_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_postponed_2954_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_diag_2955_);
v___x_2961_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2962_ = lean_st_ref_set(v___y_2923_, v___x_2961_);
v___x_2963_ = lean_box(0);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2963_);
v___x_2965_ = v___x_2930_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_dec(v_declName_2910_);
v_a_2974_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2927_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2927_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_dec(v_docComment_2911_);
lean_dec(v_declName_2910_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2994_, lean_object* v_docComment_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2994_, v_docComment_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3004_, lean_object* v_declName_3005_, lean_object* v_binders_3006_, lean_object* v_docComment_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
if (v_isVerso_3004_ == 0)
{
lean_object* v___x_3015_; 
lean_dec(v_binders_3006_);
v___x_3015_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3005_, v_docComment_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3015_;
}
else
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Lean_addVersoDocString(v_declName_3005_, v_binders_3006_, v_docComment_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3017_, lean_object* v_declName_3018_, lean_object* v_binders_3019_, lean_object* v_docComment_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
uint8_t v_isVerso_boxed_3028_; lean_object* v_res_3029_; 
v_isVerso_boxed_3028_ = lean_unbox(v_isVerso_3017_);
v_res_3029_ = l_Lean_addDocStringOf(v_isVerso_boxed_3028_, v_declName_3018_, v_binders_3019_, v_docComment_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3030_, lean_object* v_msgData_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3030_, v_msgData_3031_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3040_, lean_object* v_msgData_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3040_, v_msgData_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v_ref_3040_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3050_, lean_object* v_t_3051_){
_start:
{
if (lean_obj_tag(v_t_3051_) == 0)
{
lean_object* v_k_3052_; lean_object* v_v_3053_; lean_object* v_l_3054_; lean_object* v_r_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3709_; 
v_k_3052_ = lean_ctor_get(v_t_3051_, 1);
v_v_3053_ = lean_ctor_get(v_t_3051_, 2);
v_l_3054_ = lean_ctor_get(v_t_3051_, 3);
v_r_3055_ = lean_ctor_get(v_t_3051_, 4);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_t_3051_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_t_3051_, 0);
lean_dec(v_unused_3710_);
v___x_3057_ = v_t_3051_;
v_isShared_3058_ = v_isSharedCheck_3709_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_r_3055_);
lean_inc(v_l_3054_);
lean_inc(v_v_3053_);
lean_inc(v_k_3052_);
lean_dec(v_t_3051_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3709_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
uint8_t v___x_3059_; 
v___x_3059_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3050_, v_k_3052_);
switch(v___x_3059_)
{
case 0:
{
lean_object* v_impl_3060_; lean_object* v___x_3061_; 
v_impl_3060_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3050_, v_l_3054_);
v___x_3061_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3060_) == 0)
{
if (lean_obj_tag(v_r_3055_) == 0)
{
lean_object* v_size_3062_; lean_object* v_size_3063_; lean_object* v_k_3064_; lean_object* v_v_3065_; lean_object* v_l_3066_; lean_object* v_r_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_size_3062_ = lean_ctor_get(v_impl_3060_, 0);
lean_inc(v_size_3062_);
v_size_3063_ = lean_ctor_get(v_r_3055_, 0);
v_k_3064_ = lean_ctor_get(v_r_3055_, 1);
v_v_3065_ = lean_ctor_get(v_r_3055_, 2);
v_l_3066_ = lean_ctor_get(v_r_3055_, 3);
lean_inc(v_l_3066_);
v_r_3067_ = lean_ctor_get(v_r_3055_, 4);
v___x_3068_ = lean_unsigned_to_nat(3u);
v___x_3069_ = lean_nat_mul(v___x_3068_, v_size_3062_);
v___x_3070_ = lean_nat_dec_lt(v___x_3069_, v_size_3063_);
lean_dec(v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec(v_l_3066_);
v___x_3071_ = lean_nat_add(v___x_3061_, v_size_3062_);
lean_dec(v_size_3062_);
v___x_3072_ = lean_nat_add(v___x_3071_, v_size_3063_);
lean_dec(v___x_3071_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 3, v_impl_3060_);
lean_ctor_set(v___x_3057_, 0, v___x_3072_);
v___x_3074_ = v___x_3057_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_impl_3060_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_r_3055_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
else
{
lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3139_; 
lean_inc(v_r_3067_);
lean_inc(v_v_3065_);
lean_inc(v_k_3064_);
lean_inc(v_size_3063_);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; 
v_unused_3140_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3140_);
v_unused_3141_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_r_3055_, 2);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_r_3055_, 1);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3144_);
v___x_3077_ = v_r_3055_;
v_isShared_3078_ = v_isSharedCheck_3139_;
goto v_resetjp_3076_;
}
else
{
lean_dec(v_r_3055_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3139_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_size_3079_; lean_object* v_k_3080_; lean_object* v_v_3081_; lean_object* v_l_3082_; lean_object* v_r_3083_; lean_object* v_size_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_size_3079_ = lean_ctor_get(v_l_3066_, 0);
v_k_3080_ = lean_ctor_get(v_l_3066_, 1);
v_v_3081_ = lean_ctor_get(v_l_3066_, 2);
v_l_3082_ = lean_ctor_get(v_l_3066_, 3);
v_r_3083_ = lean_ctor_get(v_l_3066_, 4);
v_size_3084_ = lean_ctor_get(v_r_3067_, 0);
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = lean_nat_mul(v___x_3085_, v_size_3084_);
v___x_3087_ = lean_nat_dec_lt(v_size_3079_, v___x_3086_);
lean_dec(v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3115_; 
lean_inc(v_r_3083_);
lean_inc(v_l_3082_);
lean_inc(v_v_3081_);
lean_inc(v_k_3080_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_l_3066_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; 
v_unused_3116_ = lean_ctor_get(v_l_3066_, 4);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_l_3066_, 3);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_l_3066_, 2);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_l_3066_, 1);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_l_3066_, 0);
lean_dec(v_unused_3120_);
v___x_3089_ = v_l_3066_;
v_isShared_3090_ = v_isSharedCheck_3115_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v_l_3066_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3115_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3105_; 
v___x_3091_ = lean_nat_add(v___x_3061_, v_size_3062_);
lean_dec(v_size_3062_);
v___x_3092_ = lean_nat_add(v___x_3091_, v_size_3063_);
lean_dec(v_size_3063_);
if (lean_obj_tag(v_l_3082_) == 0)
{
lean_object* v_size_3113_; 
v_size_3113_ = lean_ctor_get(v_l_3082_, 0);
lean_inc(v_size_3113_);
v___y_3105_ = v_size_3113_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_unsigned_to_nat(0u);
v___y_3105_ = v___x_3114_;
goto v___jp_3104_;
}
v___jp_3093_:
{
lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3097_ = lean_nat_add(v___y_3094_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec(v___y_3094_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 4, v_r_3067_);
lean_ctor_set(v___x_3089_, 3, v_r_3083_);
lean_ctor_set(v___x_3089_, 2, v_v_3065_);
lean_ctor_set(v___x_3089_, 1, v_k_3064_);
lean_ctor_set(v___x_3089_, 0, v___x_3097_);
v___x_3099_ = v___x_3089_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_k_3064_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_v_3065_);
lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_r_3083_);
lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_r_3067_);
v___x_3099_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3101_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 4, v___x_3099_);
lean_ctor_set(v___x_3077_, 3, v___y_3095_);
lean_ctor_set(v___x_3077_, 2, v_v_3081_);
lean_ctor_set(v___x_3077_, 1, v_k_3080_);
lean_ctor_set(v___x_3077_, 0, v___x_3092_);
v___x_3101_ = v___x_3077_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3102_, 3, v___y_3095_);
lean_ctor_set(v_reuseFailAlloc_3102_, 4, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
v___jp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_nat_add(v___x_3091_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec(v___x_3091_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_l_3082_);
lean_ctor_set(v___x_3057_, 3, v_impl_3060_);
lean_ctor_set(v___x_3057_, 0, v___x_3106_);
v___x_3108_ = v___x_3057_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_impl_3060_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_l_3082_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_nat_add(v___x_3061_, v_size_3084_);
if (lean_obj_tag(v_r_3083_) == 0)
{
lean_object* v_size_3110_; 
v_size_3110_ = lean_ctor_get(v_r_3083_, 0);
lean_inc(v_size_3110_);
v___y_3094_ = v___x_3109_;
v___y_3095_ = v___x_3108_;
v___y_3096_ = v_size_3110_;
goto v___jp_3093_;
}
else
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_unsigned_to_nat(0u);
v___y_3094_ = v___x_3109_;
v___y_3095_ = v___x_3108_;
v___y_3096_ = v___x_3111_;
goto v___jp_3093_;
}
}
}
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
lean_del_object(v___x_3057_);
v___x_3121_ = lean_nat_add(v___x_3061_, v_size_3062_);
lean_dec(v_size_3062_);
v___x_3122_ = lean_nat_add(v___x_3121_, v_size_3063_);
lean_dec(v_size_3063_);
v___x_3123_ = lean_nat_add(v___x_3121_, v_size_3079_);
lean_dec(v___x_3121_);
lean_inc_ref(v_impl_3060_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 4, v_l_3066_);
lean_ctor_set(v___x_3077_, 3, v_impl_3060_);
lean_ctor_set(v___x_3077_, 2, v_v_3053_);
lean_ctor_set(v___x_3077_, 1, v_k_3052_);
lean_ctor_set(v___x_3077_, 0, v___x_3123_);
v___x_3125_ = v___x_3077_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_impl_3060_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_l_3066_);
v___x_3125_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
v_isSharedCheck_3132_ = !lean_is_exclusive(v_impl_3060_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3133_ = lean_ctor_get(v_impl_3060_, 4);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_impl_3060_, 3);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_impl_3060_, 2);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_impl_3060_, 1);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_impl_3060_, 0);
lean_dec(v_unused_3137_);
v___x_3127_ = v_impl_3060_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_dec(v_impl_3060_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 4, v_r_3067_);
lean_ctor_set(v___x_3127_, 3, v___x_3125_);
lean_ctor_set(v___x_3127_, 2, v_v_3065_);
lean_ctor_set(v___x_3127_, 1, v_k_3064_);
lean_ctor_set(v___x_3127_, 0, v___x_3122_);
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3064_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3065_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_r_3067_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3145_; lean_object* v___x_3146_; lean_object* v___x_3148_; 
v_size_3145_ = lean_ctor_get(v_impl_3060_, 0);
lean_inc(v_size_3145_);
v___x_3146_ = lean_nat_add(v___x_3061_, v_size_3145_);
lean_dec(v_size_3145_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 3, v_impl_3060_);
lean_ctor_set(v___x_3057_, 0, v___x_3146_);
v___x_3148_ = v___x_3057_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3149_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3149_, 3, v_impl_3060_);
lean_ctor_set(v_reuseFailAlloc_3149_, 4, v_r_3055_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
if (lean_obj_tag(v_r_3055_) == 0)
{
lean_object* v_l_3150_; 
v_l_3150_ = lean_ctor_get(v_r_3055_, 3);
lean_inc(v_l_3150_);
if (lean_obj_tag(v_l_3150_) == 0)
{
lean_object* v_r_3151_; 
v_r_3151_ = lean_ctor_get(v_r_3055_, 4);
lean_inc(v_r_3151_);
if (lean_obj_tag(v_r_3151_) == 0)
{
lean_object* v_size_3152_; lean_object* v_k_3153_; lean_object* v_v_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3167_; 
v_size_3152_ = lean_ctor_get(v_r_3055_, 0);
v_k_3153_ = lean_ctor_get(v_r_3055_, 1);
v_v_3154_ = lean_ctor_get(v_r_3055_, 2);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3168_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3169_);
v___x_3156_ = v_r_3055_;
v_isShared_3157_ = v_isSharedCheck_3167_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_v_3154_);
lean_inc(v_k_3153_);
lean_inc(v_size_3152_);
lean_dec(v_r_3055_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3167_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_size_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v_size_3158_ = lean_ctor_get(v_l_3150_, 0);
v___x_3159_ = lean_nat_add(v___x_3061_, v_size_3152_);
lean_dec(v_size_3152_);
v___x_3160_ = lean_nat_add(v___x_3061_, v_size_3158_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 4, v_l_3150_);
lean_ctor_set(v___x_3156_, 3, v_impl_3060_);
lean_ctor_set(v___x_3156_, 2, v_v_3053_);
lean_ctor_set(v___x_3156_, 1, v_k_3052_);
lean_ctor_set(v___x_3156_, 0, v___x_3160_);
v___x_3162_ = v___x_3156_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3166_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3166_, 3, v_impl_3060_);
lean_ctor_set(v_reuseFailAlloc_3166_, 4, v_l_3150_);
v___x_3162_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3164_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_r_3151_);
lean_ctor_set(v___x_3057_, 3, v___x_3162_);
lean_ctor_set(v___x_3057_, 2, v_v_3154_);
lean_ctor_set(v___x_3057_, 1, v_k_3153_);
lean_ctor_set(v___x_3057_, 0, v___x_3159_);
v___x_3164_ = v___x_3057_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_k_3153_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_v_3154_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_r_3151_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
else
{
lean_object* v_k_3170_; lean_object* v_v_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3194_; 
v_k_3170_ = lean_ctor_get(v_r_3055_, 1);
v_v_3171_ = lean_ctor_get(v_r_3055_, 2);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; lean_object* v_unused_3196_; lean_object* v_unused_3197_; 
v_unused_3195_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3195_);
v_unused_3196_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3196_);
v_unused_3197_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3197_);
v___x_3173_ = v_r_3055_;
v_isShared_3174_ = v_isSharedCheck_3194_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_v_3171_);
lean_inc(v_k_3170_);
lean_dec(v_r_3055_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3194_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_k_3175_; lean_object* v_v_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3190_; 
v_k_3175_ = lean_ctor_get(v_l_3150_, 1);
v_v_3176_ = lean_ctor_get(v_l_3150_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_l_3150_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; lean_object* v_unused_3192_; lean_object* v_unused_3193_; 
v_unused_3191_ = lean_ctor_get(v_l_3150_, 4);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v_l_3150_, 3);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v_l_3150_, 0);
lean_dec(v_unused_3193_);
v___x_3178_ = v_l_3150_;
v_isShared_3179_ = v_isSharedCheck_3190_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_v_3176_);
lean_inc(v_k_3175_);
lean_dec(v_l_3150_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3190_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_unsigned_to_nat(3u);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 4, v_r_3151_);
lean_ctor_set(v___x_3178_, 3, v_r_3151_);
lean_ctor_set(v___x_3178_, 2, v_v_3053_);
lean_ctor_set(v___x_3178_, 1, v_k_3052_);
lean_ctor_set(v___x_3178_, 0, v___x_3061_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_r_3151_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_r_3151_);
v___x_3182_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 3, v_r_3151_);
lean_ctor_set(v___x_3173_, 0, v___x_3061_);
v___x_3184_ = v___x_3173_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_k_3170_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_v_3171_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_r_3151_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_r_3151_);
v___x_3184_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3186_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v___x_3184_);
lean_ctor_set(v___x_3057_, 3, v___x_3182_);
lean_ctor_set(v___x_3057_, 2, v_v_3176_);
lean_ctor_set(v___x_3057_, 1, v_k_3175_);
lean_ctor_set(v___x_3057_, 0, v___x_3180_);
v___x_3186_ = v___x_3057_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_k_3175_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_v_3176_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3198_; 
v_r_3198_ = lean_ctor_get(v_r_3055_, 4);
lean_inc(v_r_3198_);
if (lean_obj_tag(v_r_3198_) == 0)
{
lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3211_; 
v_k_3199_ = lean_ctor_get(v_r_3055_, 1);
v_v_3200_ = lean_ctor_get(v_r_3055_, 2);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; lean_object* v_unused_3213_; lean_object* v_unused_3214_; 
v_unused_3212_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3213_);
v_unused_3214_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3214_);
v___x_3202_ = v_r_3055_;
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_v_3200_);
lean_inc(v_k_3199_);
lean_dec(v_r_3055_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3211_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3204_ = lean_unsigned_to_nat(3u);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v_l_3150_);
lean_ctor_set(v___x_3202_, 2, v_v_3053_);
lean_ctor_set(v___x_3202_, 1, v_k_3052_);
lean_ctor_set(v___x_3202_, 0, v___x_3061_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v_l_3150_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v_l_3150_);
v___x_3206_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_r_3198_);
lean_ctor_set(v___x_3057_, 3, v___x_3206_);
lean_ctor_set(v___x_3057_, 2, v_v_3200_);
lean_ctor_set(v___x_3057_, 1, v_k_3199_);
lean_ctor_set(v___x_3057_, 0, v___x_3204_);
v___x_3208_ = v___x_3057_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_k_3199_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_v_3200_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v_r_3198_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_size_3215_; lean_object* v_k_3216_; lean_object* v_v_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3228_; 
v_size_3215_ = lean_ctor_get(v_r_3055_, 0);
v_k_3216_ = lean_ctor_get(v_r_3055_, 1);
v_v_3217_ = lean_ctor_get(v_r_3055_, 2);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; lean_object* v_unused_3230_; 
v_unused_3229_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3230_);
v___x_3219_ = v_r_3055_;
v_isShared_3220_ = v_isSharedCheck_3228_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_v_3217_);
lean_inc(v_k_3216_);
lean_inc(v_size_3215_);
lean_dec(v_r_3055_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3228_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 3, v_r_3198_);
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_size_3215_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_k_3216_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_v_3217_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_r_3198_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_r_3198_);
v___x_3222_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_unsigned_to_nat(2u);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v___x_3222_);
lean_ctor_set(v___x_3057_, 3, v_r_3198_);
lean_ctor_set(v___x_3057_, 0, v___x_3223_);
v___x_3225_ = v___x_3057_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_r_3198_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v___x_3222_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
}
else
{
lean_object* v___x_3232_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 3, v_r_3055_);
lean_ctor_set(v___x_3057_, 0, v___x_3061_);
v___x_3232_ = v___x_3057_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_r_3055_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_r_3055_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3057_);
lean_dec(v_v_3053_);
lean_dec(v_k_3052_);
if (lean_obj_tag(v_l_3054_) == 0)
{
if (lean_obj_tag(v_r_3055_) == 0)
{
lean_object* v_size_3234_; lean_object* v_k_3235_; lean_object* v_v_3236_; lean_object* v_l_3237_; lean_object* v_r_3238_; lean_object* v_size_3239_; lean_object* v_k_3240_; lean_object* v_v_3241_; lean_object* v_l_3242_; lean_object* v_r_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_size_3234_ = lean_ctor_get(v_l_3054_, 0);
v_k_3235_ = lean_ctor_get(v_l_3054_, 1);
v_v_3236_ = lean_ctor_get(v_l_3054_, 2);
v_l_3237_ = lean_ctor_get(v_l_3054_, 3);
v_r_3238_ = lean_ctor_get(v_l_3054_, 4);
lean_inc(v_r_3238_);
v_size_3239_ = lean_ctor_get(v_r_3055_, 0);
v_k_3240_ = lean_ctor_get(v_r_3055_, 1);
v_v_3241_ = lean_ctor_get(v_r_3055_, 2);
v_l_3242_ = lean_ctor_get(v_r_3055_, 3);
lean_inc(v_l_3242_);
v_r_3243_ = lean_ctor_get(v_r_3055_, 4);
v___x_3244_ = lean_unsigned_to_nat(1u);
v___x_3245_ = lean_nat_dec_lt(v_size_3234_, v_size_3239_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3381_; 
lean_inc(v_l_3237_);
lean_inc(v_v_3236_);
lean_inc(v_k_3235_);
v_isSharedCheck_3381_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; lean_object* v_unused_3386_; 
v_unused_3382_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_l_3054_, 2);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_l_3054_, 1);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3386_);
v___x_3247_ = v_l_3054_;
v_isShared_3248_ = v_isSharedCheck_3381_;
goto v_resetjp_3246_;
}
else
{
lean_dec(v_l_3054_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3381_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v_tree_3250_; 
v___x_3249_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3235_, v_v_3236_, v_l_3237_, v_r_3238_);
v_tree_3250_ = lean_ctor_get(v___x_3249_, 2);
lean_inc(v_tree_3250_);
if (lean_obj_tag(v_tree_3250_) == 0)
{
lean_object* v_k_3251_; lean_object* v_v_3252_; lean_object* v_size_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_k_3251_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_k_3251_);
v_v_3252_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_v_3252_);
lean_dec_ref(v___x_3249_);
v_size_3253_ = lean_ctor_get(v_tree_3250_, 0);
v___x_3254_ = lean_unsigned_to_nat(3u);
v___x_3255_ = lean_nat_mul(v___x_3254_, v_size_3253_);
v___x_3256_ = lean_nat_dec_lt(v___x_3255_, v_size_3239_);
lean_dec(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_dec(v_l_3242_);
v___x_3257_ = lean_nat_add(v___x_3244_, v_size_3253_);
v___x_3258_ = lean_nat_add(v___x_3257_, v_size_3239_);
lean_dec(v___x_3257_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v_r_3055_);
lean_ctor_set(v___x_3247_, 3, v_tree_3250_);
lean_ctor_set(v___x_3247_, 2, v_v_3252_);
lean_ctor_set(v___x_3247_, 1, v_k_3251_);
lean_ctor_set(v___x_3247_, 0, v___x_3258_);
v___x_3260_ = v___x_3247_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3261_, 1, v_k_3251_);
lean_ctor_set(v_reuseFailAlloc_3261_, 2, v_v_3252_);
lean_ctor_set(v_reuseFailAlloc_3261_, 3, v_tree_3250_);
lean_ctor_set(v_reuseFailAlloc_3261_, 4, v_r_3055_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
else
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3316_; 
lean_inc(v_r_3243_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
lean_inc(v_size_3239_);
v_isSharedCheck_3316_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; lean_object* v_unused_3321_; 
v_unused_3317_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_r_3055_, 2);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_r_3055_, 1);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3321_);
v___x_3263_ = v_r_3055_;
v_isShared_3264_ = v_isSharedCheck_3316_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v_r_3055_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3316_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v_size_3265_; lean_object* v_k_3266_; lean_object* v_v_3267_; lean_object* v_l_3268_; lean_object* v_r_3269_; lean_object* v_size_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v_size_3265_ = lean_ctor_get(v_l_3242_, 0);
v_k_3266_ = lean_ctor_get(v_l_3242_, 1);
v_v_3267_ = lean_ctor_get(v_l_3242_, 2);
v_l_3268_ = lean_ctor_get(v_l_3242_, 3);
v_r_3269_ = lean_ctor_get(v_l_3242_, 4);
v_size_3270_ = lean_ctor_get(v_r_3243_, 0);
v___x_3271_ = lean_unsigned_to_nat(2u);
v___x_3272_ = lean_nat_mul(v___x_3271_, v_size_3270_);
v___x_3273_ = lean_nat_dec_lt(v_size_3265_, v___x_3272_);
lean_dec(v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3301_; 
lean_inc(v_r_3269_);
lean_inc(v_l_3268_);
lean_inc(v_v_3267_);
lean_inc(v_k_3266_);
v_isSharedCheck_3301_ = !lean_is_exclusive(v_l_3242_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3302_ = lean_ctor_get(v_l_3242_, 4);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3242_, 3);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_3242_, 2);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_3242_, 1);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_3242_, 0);
lean_dec(v_unused_3306_);
v___x_3275_ = v_l_3242_;
v_isShared_3276_ = v_isSharedCheck_3301_;
goto v_resetjp_3274_;
}
else
{
lean_dec(v_l_3242_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3301_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3291_; 
v___x_3277_ = lean_nat_add(v___x_3244_, v_size_3253_);
v___x_3278_ = lean_nat_add(v___x_3277_, v_size_3239_);
lean_dec(v_size_3239_);
if (lean_obj_tag(v_l_3268_) == 0)
{
lean_object* v_size_3299_; 
v_size_3299_ = lean_ctor_get(v_l_3268_, 0);
lean_inc(v_size_3299_);
v___y_3291_ = v_size_3299_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_unsigned_to_nat(0u);
v___y_3291_ = v___x_3300_;
goto v___jp_3290_;
}
v___jp_3279_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3283_ = lean_nat_add(v___y_3280_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec(v___y_3280_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 4, v_r_3243_);
lean_ctor_set(v___x_3275_, 3, v_r_3269_);
lean_ctor_set(v___x_3275_, 2, v_v_3241_);
lean_ctor_set(v___x_3275_, 1, v_k_3240_);
lean_ctor_set(v___x_3275_, 0, v___x_3283_);
v___x_3285_ = v___x_3275_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3289_, 3, v_r_3269_);
lean_ctor_set(v_reuseFailAlloc_3289_, 4, v_r_3243_);
v___x_3285_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3287_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 4, v___x_3285_);
lean_ctor_set(v___x_3263_, 3, v___y_3281_);
lean_ctor_set(v___x_3263_, 2, v_v_3267_);
lean_ctor_set(v___x_3263_, 1, v_k_3266_);
lean_ctor_set(v___x_3263_, 0, v___x_3278_);
v___x_3287_ = v___x_3263_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_k_3266_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v_v_3267_);
lean_ctor_set(v_reuseFailAlloc_3288_, 3, v___y_3281_);
lean_ctor_set(v_reuseFailAlloc_3288_, 4, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
v___jp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3292_ = lean_nat_add(v___x_3277_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec(v___x_3277_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v_l_3268_);
lean_ctor_set(v___x_3247_, 3, v_tree_3250_);
lean_ctor_set(v___x_3247_, 2, v_v_3252_);
lean_ctor_set(v___x_3247_, 1, v_k_3251_);
lean_ctor_set(v___x_3247_, 0, v___x_3292_);
v___x_3294_ = v___x_3247_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v_k_3251_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v_v_3252_);
lean_ctor_set(v_reuseFailAlloc_3298_, 3, v_tree_3250_);
lean_ctor_set(v_reuseFailAlloc_3298_, 4, v_l_3268_);
v___x_3294_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; 
v___x_3295_ = lean_nat_add(v___x_3244_, v_size_3270_);
if (lean_obj_tag(v_r_3269_) == 0)
{
lean_object* v_size_3296_; 
v_size_3296_ = lean_ctor_get(v_r_3269_, 0);
lean_inc(v_size_3296_);
v___y_3280_ = v___x_3295_;
v___y_3281_ = v___x_3294_;
v___y_3282_ = v_size_3296_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_unsigned_to_nat(0u);
v___y_3280_ = v___x_3295_;
v___y_3281_ = v___x_3294_;
v___y_3282_ = v___x_3297_;
goto v___jp_3279_;
}
}
}
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3307_ = lean_nat_add(v___x_3244_, v_size_3253_);
v___x_3308_ = lean_nat_add(v___x_3307_, v_size_3239_);
lean_dec(v_size_3239_);
v___x_3309_ = lean_nat_add(v___x_3307_, v_size_3265_);
lean_dec(v___x_3307_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 4, v_l_3242_);
lean_ctor_set(v___x_3263_, 3, v_tree_3250_);
lean_ctor_set(v___x_3263_, 2, v_v_3252_);
lean_ctor_set(v___x_3263_, 1, v_k_3251_);
lean_ctor_set(v___x_3263_, 0, v___x_3309_);
v___x_3311_ = v___x_3263_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_k_3251_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_v_3252_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_tree_3250_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_l_3242_);
v___x_3311_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v_r_3243_);
lean_ctor_set(v___x_3247_, 3, v___x_3311_);
lean_ctor_set(v___x_3247_, 2, v_v_3241_);
lean_ctor_set(v___x_3247_, 1, v_k_3240_);
lean_ctor_set(v___x_3247_, 0, v___x_3308_);
v___x_3313_ = v___x_3247_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3243_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
else
{
lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3375_; 
lean_inc(v_r_3243_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
lean_inc(v_size_3239_);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; 
v_unused_3376_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_r_3055_, 2);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_r_3055_, 1);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3380_);
v___x_3323_ = v_r_3055_;
v_isShared_3324_ = v_isSharedCheck_3375_;
goto v_resetjp_3322_;
}
else
{
lean_dec(v_r_3055_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3375_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
if (lean_obj_tag(v_l_3242_) == 0)
{
if (lean_obj_tag(v_r_3243_) == 0)
{
lean_object* v_k_3325_; lean_object* v_v_3326_; lean_object* v_size_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v_k_3325_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_k_3325_);
v_v_3326_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_v_3326_);
lean_dec_ref(v___x_3249_);
v_size_3327_ = lean_ctor_get(v_l_3242_, 0);
v___x_3328_ = lean_nat_add(v___x_3244_, v_size_3239_);
lean_dec(v_size_3239_);
v___x_3329_ = lean_nat_add(v___x_3244_, v_size_3327_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 4, v_l_3242_);
lean_ctor_set(v___x_3323_, 3, v_tree_3250_);
lean_ctor_set(v___x_3323_, 2, v_v_3326_);
lean_ctor_set(v___x_3323_, 1, v_k_3325_);
lean_ctor_set(v___x_3323_, 0, v___x_3329_);
v___x_3331_ = v___x_3323_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3325_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3326_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_tree_3250_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_l_3242_);
v___x_3331_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
lean_object* v___x_3333_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v_r_3243_);
lean_ctor_set(v___x_3247_, 3, v___x_3331_);
lean_ctor_set(v___x_3247_, 2, v_v_3241_);
lean_ctor_set(v___x_3247_, 1, v_k_3240_);
lean_ctor_set(v___x_3247_, 0, v___x_3328_);
v___x_3333_ = v___x_3247_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v___x_3331_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3243_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
else
{
lean_object* v_k_3336_; lean_object* v_v_3337_; lean_object* v_k_3338_; lean_object* v_v_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_size_3239_);
v_k_3336_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_k_3336_);
v_v_3337_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_v_3337_);
lean_dec_ref(v___x_3249_);
v_k_3338_ = lean_ctor_get(v_l_3242_, 1);
v_v_3339_ = lean_ctor_get(v_l_3242_, 2);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_l_3242_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; lean_object* v_unused_3355_; lean_object* v_unused_3356_; 
v_unused_3354_ = lean_ctor_get(v_l_3242_, 4);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_l_3242_, 3);
lean_dec(v_unused_3355_);
v_unused_3356_ = lean_ctor_get(v_l_3242_, 0);
lean_dec(v_unused_3356_);
v___x_3341_ = v_l_3242_;
v_isShared_3342_ = v_isSharedCheck_3353_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_v_3339_);
lean_inc(v_k_3338_);
lean_dec(v_l_3242_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3353_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3343_ = lean_unsigned_to_nat(3u);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 4, v_r_3243_);
lean_ctor_set(v___x_3341_, 3, v_r_3243_);
lean_ctor_set(v___x_3341_, 2, v_v_3337_);
lean_ctor_set(v___x_3341_, 1, v_k_3336_);
lean_ctor_set(v___x_3341_, 0, v___x_3244_);
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_k_3336_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_v_3337_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v_r_3243_);
v___x_3345_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 3, v_r_3243_);
lean_ctor_set(v___x_3323_, 0, v___x_3244_);
v___x_3347_ = v___x_3323_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_r_3243_);
v___x_3347_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3349_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v___x_3347_);
lean_ctor_set(v___x_3247_, 3, v___x_3345_);
lean_ctor_set(v___x_3247_, 2, v_v_3339_);
lean_ctor_set(v___x_3247_, 1, v_k_3338_);
lean_ctor_set(v___x_3247_, 0, v___x_3343_);
v___x_3349_ = v___x_3247_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3243_) == 0)
{
lean_object* v_k_3357_; lean_object* v_v_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
lean_dec(v_size_3239_);
v_k_3357_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_k_3357_);
v_v_3358_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_v_3358_);
lean_dec_ref(v___x_3249_);
v___x_3359_ = lean_unsigned_to_nat(3u);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 4, v_l_3242_);
lean_ctor_set(v___x_3323_, 2, v_v_3358_);
lean_ctor_set(v___x_3323_, 1, v_k_3357_);
lean_ctor_set(v___x_3323_, 0, v___x_3244_);
v___x_3361_ = v___x_3323_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3365_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3365_, 3, v_l_3242_);
lean_ctor_set(v_reuseFailAlloc_3365_, 4, v_l_3242_);
v___x_3361_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v_r_3243_);
lean_ctor_set(v___x_3247_, 3, v___x_3361_);
lean_ctor_set(v___x_3247_, 2, v_v_3241_);
lean_ctor_set(v___x_3247_, 1, v_k_3240_);
lean_ctor_set(v___x_3247_, 0, v___x_3359_);
v___x_3363_ = v___x_3247_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_r_3243_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_object* v_k_3366_; lean_object* v_v_3367_; lean_object* v___x_3369_; 
v_k_3366_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_k_3366_);
v_v_3367_ = lean_ctor_get(v___x_3249_, 1);
lean_inc(v_v_3367_);
lean_dec_ref(v___x_3249_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 3, v_r_3243_);
v___x_3369_ = v___x_3323_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_size_3239_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_k_3240_);
lean_ctor_set(v_reuseFailAlloc_3374_, 2, v_v_3241_);
lean_ctor_set(v_reuseFailAlloc_3374_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3374_, 4, v_r_3243_);
v___x_3369_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_unsigned_to_nat(2u);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 4, v___x_3369_);
lean_ctor_set(v___x_3247_, 3, v_r_3243_);
lean_ctor_set(v___x_3247_, 2, v_v_3367_);
lean_ctor_set(v___x_3247_, 1, v_k_3366_);
lean_ctor_set(v___x_3247_, 0, v___x_3370_);
v___x_3372_ = v___x_3247_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_k_3366_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_v_3367_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_r_3243_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v___x_3369_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
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
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3539_; 
lean_inc(v_r_3243_);
lean_inc(v_v_3241_);
lean_inc(v_k_3240_);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; lean_object* v_unused_3541_; lean_object* v_unused_3542_; lean_object* v_unused_3543_; lean_object* v_unused_3544_; 
v_unused_3540_ = lean_ctor_get(v_r_3055_, 4);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_r_3055_, 3);
lean_dec(v_unused_3541_);
v_unused_3542_ = lean_ctor_get(v_r_3055_, 2);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_r_3055_, 1);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_r_3055_, 0);
lean_dec(v_unused_3544_);
v___x_3388_ = v_r_3055_;
v_isShared_3389_ = v_isSharedCheck_3539_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_r_3055_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3539_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v_tree_3391_; 
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3240_, v_v_3241_, v_l_3242_, v_r_3243_);
v_tree_3391_ = lean_ctor_get(v___x_3390_, 2);
lean_inc(v_tree_3391_);
if (lean_obj_tag(v_tree_3391_) == 0)
{
lean_object* v_k_3392_; lean_object* v_v_3393_; lean_object* v_size_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_k_3392_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_k_3392_);
v_v_3393_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_v_3393_);
lean_dec_ref(v___x_3390_);
v_size_3394_ = lean_ctor_get(v_tree_3391_, 0);
v___x_3395_ = lean_unsigned_to_nat(3u);
v___x_3396_ = lean_nat_mul(v___x_3395_, v_size_3394_);
v___x_3397_ = lean_nat_dec_lt(v___x_3396_, v_size_3234_);
lean_dec(v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
lean_dec(v_r_3238_);
v___x_3398_ = lean_nat_add(v___x_3244_, v_size_3234_);
v___x_3399_ = lean_nat_add(v___x_3398_, v_size_3394_);
lean_dec(v___x_3398_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_tree_3391_);
lean_ctor_set(v___x_3388_, 3, v_l_3054_);
lean_ctor_set(v___x_3388_, 2, v_v_3393_);
lean_ctor_set(v___x_3388_, 1, v_k_3392_);
lean_ctor_set(v___x_3388_, 0, v___x_3399_);
v___x_3401_ = v___x_3388_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_k_3392_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_v_3393_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_tree_3391_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
else
{
lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3468_; 
lean_inc(v_l_3237_);
lean_inc(v_v_3236_);
lean_inc(v_k_3235_);
lean_inc(v_size_3234_);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; lean_object* v_unused_3470_; lean_object* v_unused_3471_; lean_object* v_unused_3472_; lean_object* v_unused_3473_; 
v_unused_3469_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_l_3054_, 2);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_l_3054_, 1);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3473_);
v___x_3404_ = v_l_3054_;
v_isShared_3405_ = v_isSharedCheck_3468_;
goto v_resetjp_3403_;
}
else
{
lean_dec(v_l_3054_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3468_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_size_3406_; lean_object* v_size_3407_; lean_object* v_k_3408_; lean_object* v_v_3409_; lean_object* v_l_3410_; lean_object* v_r_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_size_3406_ = lean_ctor_get(v_l_3237_, 0);
v_size_3407_ = lean_ctor_get(v_r_3238_, 0);
v_k_3408_ = lean_ctor_get(v_r_3238_, 1);
v_v_3409_ = lean_ctor_get(v_r_3238_, 2);
v_l_3410_ = lean_ctor_get(v_r_3238_, 3);
v_r_3411_ = lean_ctor_get(v_r_3238_, 4);
v___x_3412_ = lean_unsigned_to_nat(2u);
v___x_3413_ = lean_nat_mul(v___x_3412_, v_size_3406_);
v___x_3414_ = lean_nat_dec_lt(v_size_3407_, v___x_3413_);
lean_dec(v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3452_; 
lean_inc(v_r_3411_);
lean_inc(v_l_3410_);
lean_inc(v_v_3409_);
lean_inc(v_k_3408_);
lean_del_object(v___x_3404_);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_r_3238_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3453_ = lean_ctor_get(v_r_3238_, 4);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_r_3238_, 3);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_r_3238_, 2);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_r_3238_, 1);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_r_3238_, 0);
lean_dec(v_unused_3457_);
v___x_3416_ = v_r_3238_;
v_isShared_3417_ = v_isSharedCheck_3452_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v_r_3238_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3452_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___x_3440_; lean_object* v___y_3442_; 
v___x_3418_ = lean_nat_add(v___x_3244_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3419_ = lean_nat_add(v___x_3418_, v_size_3394_);
lean_dec(v___x_3418_);
v___x_3440_ = lean_nat_add(v___x_3244_, v_size_3406_);
if (lean_obj_tag(v_l_3410_) == 0)
{
lean_object* v_size_3450_; 
v_size_3450_ = lean_ctor_get(v_l_3410_, 0);
lean_inc(v_size_3450_);
v___y_3442_ = v_size_3450_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___y_3442_ = v___x_3451_;
goto v___jp_3441_;
}
v___jp_3420_:
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3424_ = lean_nat_add(v___y_3421_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec(v___y_3421_);
lean_inc_ref(v_tree_3391_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 4, v_tree_3391_);
lean_ctor_set(v___x_3416_, 3, v_r_3411_);
lean_ctor_set(v___x_3416_, 2, v_v_3393_);
lean_ctor_set(v___x_3416_, 1, v_k_3392_);
lean_ctor_set(v___x_3416_, 0, v___x_3424_);
v___x_3426_ = v___x_3416_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_k_3392_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_v_3393_);
lean_ctor_set(v_reuseFailAlloc_3439_, 3, v_r_3411_);
lean_ctor_set(v_reuseFailAlloc_3439_, 4, v_tree_3391_);
v___x_3426_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_isSharedCheck_3433_ = !lean_is_exclusive(v_tree_3391_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; lean_object* v_unused_3435_; lean_object* v_unused_3436_; lean_object* v_unused_3437_; lean_object* v_unused_3438_; 
v_unused_3434_ = lean_ctor_get(v_tree_3391_, 4);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v_tree_3391_, 3);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_tree_3391_, 2);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_tree_3391_, 1);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_tree_3391_, 0);
lean_dec(v_unused_3438_);
v___x_3428_ = v_tree_3391_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_dec(v_tree_3391_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 4, v___x_3426_);
lean_ctor_set(v___x_3428_, 3, v___y_3422_);
lean_ctor_set(v___x_3428_, 2, v_v_3409_);
lean_ctor_set(v___x_3428_, 1, v_k_3408_);
lean_ctor_set(v___x_3428_, 0, v___x_3419_);
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_3408_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_3409_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v___y_3422_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v___x_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
v___jp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_nat_add(v___x_3440_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec(v___x_3440_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_l_3410_);
lean_ctor_set(v___x_3388_, 3, v_l_3237_);
lean_ctor_set(v___x_3388_, 2, v_v_3236_);
lean_ctor_set(v___x_3388_, 1, v_k_3235_);
lean_ctor_set(v___x_3388_, 0, v___x_3443_);
v___x_3445_ = v___x_3388_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_l_3410_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_nat_add(v___x_3244_, v_size_3394_);
if (lean_obj_tag(v_r_3411_) == 0)
{
lean_object* v_size_3447_; 
v_size_3447_ = lean_ctor_get(v_r_3411_, 0);
lean_inc(v_size_3447_);
v___y_3421_ = v___x_3446_;
v___y_3422_ = v___x_3445_;
v___y_3423_ = v_size_3447_;
goto v___jp_3420_;
}
else
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___y_3421_ = v___x_3446_;
v___y_3422_ = v___x_3445_;
v___y_3423_ = v___x_3448_;
goto v___jp_3420_;
}
}
}
}
}
else
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3458_ = lean_nat_add(v___x_3244_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3459_ = lean_nat_add(v___x_3458_, v_size_3394_);
lean_dec(v___x_3458_);
v___x_3460_ = lean_nat_add(v___x_3244_, v_size_3394_);
v___x_3461_ = lean_nat_add(v___x_3460_, v_size_3407_);
lean_dec(v___x_3460_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_tree_3391_);
lean_ctor_set(v___x_3388_, 3, v_r_3238_);
lean_ctor_set(v___x_3388_, 2, v_v_3393_);
lean_ctor_set(v___x_3388_, 1, v_k_3392_);
lean_ctor_set(v___x_3388_, 0, v___x_3461_);
v___x_3463_ = v___x_3388_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_k_3392_);
lean_ctor_set(v_reuseFailAlloc_3467_, 2, v_v_3393_);
lean_ctor_set(v_reuseFailAlloc_3467_, 3, v_r_3238_);
lean_ctor_set(v_reuseFailAlloc_3467_, 4, v_tree_3391_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 4, v___x_3463_);
lean_ctor_set(v___x_3404_, 0, v___x_3459_);
v___x_3465_ = v___x_3404_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3466_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3466_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3466_, 4, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3237_) == 0)
{
lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3497_; 
lean_inc_ref(v_l_3237_);
lean_inc(v_v_3236_);
lean_inc(v_k_3235_);
lean_inc(v_size_3234_);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; lean_object* v_unused_3501_; lean_object* v_unused_3502_; 
v_unused_3498_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_l_3054_, 2);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v_l_3054_, 1);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3502_);
v___x_3475_ = v_l_3054_;
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
else
{
lean_dec(v_l_3054_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3497_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_r_3238_) == 0)
{
lean_object* v_k_3477_; lean_object* v_v_3478_; lean_object* v_size_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v_k_3477_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_k_3477_);
v_v_3478_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_v_3478_);
lean_dec_ref(v___x_3390_);
v_size_3479_ = lean_ctor_get(v_r_3238_, 0);
v___x_3480_ = lean_nat_add(v___x_3244_, v_size_3234_);
lean_dec(v_size_3234_);
v___x_3481_ = lean_nat_add(v___x_3244_, v_size_3479_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_tree_3391_);
lean_ctor_set(v___x_3388_, 3, v_r_3238_);
lean_ctor_set(v___x_3388_, 2, v_v_3478_);
lean_ctor_set(v___x_3388_, 1, v_k_3477_);
lean_ctor_set(v___x_3388_, 0, v___x_3481_);
v___x_3483_ = v___x_3388_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3477_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3478_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_r_3238_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_tree_3391_);
v___x_3483_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3485_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 4, v___x_3483_);
lean_ctor_set(v___x_3475_, 0, v___x_3480_);
v___x_3485_ = v___x_3475_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
else
{
lean_object* v_k_3488_; lean_object* v_v_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_dec(v_size_3234_);
v_k_3488_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_k_3488_);
v_v_3489_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_v_3489_);
lean_dec_ref(v___x_3390_);
v___x_3490_ = lean_unsigned_to_nat(3u);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_r_3238_);
lean_ctor_set(v___x_3388_, 3, v_r_3238_);
lean_ctor_set(v___x_3388_, 2, v_v_3489_);
lean_ctor_set(v___x_3388_, 1, v_k_3488_);
lean_ctor_set(v___x_3388_, 0, v___x_3244_);
v___x_3492_ = v___x_3388_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_r_3238_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_r_3238_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 4, v___x_3492_);
lean_ctor_set(v___x_3475_, 0, v___x_3490_);
v___x_3494_ = v___x_3475_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3238_) == 0)
{
lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3527_; 
lean_inc(v_l_3237_);
lean_inc(v_v_3236_);
lean_inc(v_k_3235_);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; lean_object* v_unused_3529_; lean_object* v_unused_3530_; lean_object* v_unused_3531_; lean_object* v_unused_3532_; 
v_unused_3528_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3529_);
v_unused_3530_ = lean_ctor_get(v_l_3054_, 2);
lean_dec(v_unused_3530_);
v_unused_3531_ = lean_ctor_get(v_l_3054_, 1);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3532_);
v___x_3504_ = v_l_3054_;
v_isShared_3505_ = v_isSharedCheck_3527_;
goto v_resetjp_3503_;
}
else
{
lean_dec(v_l_3054_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3527_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_k_3506_; lean_object* v_v_3507_; lean_object* v_k_3508_; lean_object* v_v_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3523_; 
v_k_3506_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_k_3506_);
v_v_3507_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_v_3507_);
lean_dec_ref(v___x_3390_);
v_k_3508_ = lean_ctor_get(v_r_3238_, 1);
v_v_3509_ = lean_ctor_get(v_r_3238_, 2);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_r_3238_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; lean_object* v_unused_3525_; lean_object* v_unused_3526_; 
v_unused_3524_ = lean_ctor_get(v_r_3238_, 4);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_r_3238_, 3);
lean_dec(v_unused_3525_);
v_unused_3526_ = lean_ctor_get(v_r_3238_, 0);
lean_dec(v_unused_3526_);
v___x_3511_ = v_r_3238_;
v_isShared_3512_ = v_isSharedCheck_3523_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_v_3509_);
lean_inc(v_k_3508_);
lean_dec(v_r_3238_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3523_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = lean_unsigned_to_nat(3u);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 4, v_l_3237_);
lean_ctor_set(v___x_3511_, 3, v_l_3237_);
lean_ctor_set(v___x_3511_, 2, v_v_3236_);
lean_ctor_set(v___x_3511_, 1, v_k_3235_);
lean_ctor_set(v___x_3511_, 0, v___x_3244_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_k_3235_);
lean_ctor_set(v_reuseFailAlloc_3522_, 2, v_v_3236_);
lean_ctor_set(v_reuseFailAlloc_3522_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3522_, 4, v_l_3237_);
v___x_3515_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3517_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_l_3237_);
lean_ctor_set(v___x_3388_, 3, v_l_3237_);
lean_ctor_set(v___x_3388_, 2, v_v_3507_);
lean_ctor_set(v___x_3388_, 1, v_k_3506_);
lean_ctor_set(v___x_3388_, 0, v___x_3244_);
v___x_3517_ = v___x_3388_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3506_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3507_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_l_3237_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_l_3237_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 4, v___x_3517_);
lean_ctor_set(v___x_3504_, 3, v___x_3515_);
lean_ctor_set(v___x_3504_, 2, v_v_3509_);
lean_ctor_set(v___x_3504_, 1, v_k_3508_);
lean_ctor_set(v___x_3504_, 0, v___x_3513_);
v___x_3519_ = v___x_3504_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_k_3508_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_v_3509_);
lean_ctor_set(v_reuseFailAlloc_3520_, 3, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3520_, 4, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
else
{
lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v___x_3535_; lean_object* v___x_3537_; 
v_k_3533_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_k_3533_);
v_v_3534_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_v_3534_);
lean_dec_ref(v___x_3390_);
v___x_3535_ = lean_unsigned_to_nat(2u);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_r_3238_);
lean_ctor_set(v___x_3388_, 3, v_l_3054_);
lean_ctor_set(v___x_3388_, 2, v_v_3534_);
lean_ctor_set(v___x_3388_, 1, v_k_3533_);
lean_ctor_set(v___x_3388_, 0, v___x_3535_);
v___x_3537_ = v___x_3388_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3533_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3534_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_r_3238_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
}
else
{
return v_l_3054_;
}
}
else
{
return v_r_3055_;
}
}
default: 
{
lean_object* v_impl_3545_; lean_object* v___x_3546_; 
v_impl_3545_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3050_, v_r_3055_);
v___x_3546_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3545_) == 0)
{
if (lean_obj_tag(v_l_3054_) == 0)
{
lean_object* v_size_3547_; lean_object* v_size_3548_; lean_object* v_k_3549_; lean_object* v_v_3550_; lean_object* v_l_3551_; lean_object* v_r_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v_size_3547_ = lean_ctor_get(v_impl_3545_, 0);
lean_inc(v_size_3547_);
v_size_3548_ = lean_ctor_get(v_l_3054_, 0);
v_k_3549_ = lean_ctor_get(v_l_3054_, 1);
v_v_3550_ = lean_ctor_get(v_l_3054_, 2);
v_l_3551_ = lean_ctor_get(v_l_3054_, 3);
v_r_3552_ = lean_ctor_get(v_l_3054_, 4);
lean_inc(v_r_3552_);
v___x_3553_ = lean_unsigned_to_nat(3u);
v___x_3554_ = lean_nat_mul(v___x_3553_, v_size_3547_);
v___x_3555_ = lean_nat_dec_lt(v___x_3554_, v_size_3548_);
lean_dec(v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_dec(v_r_3552_);
v___x_3556_ = lean_nat_add(v___x_3546_, v_size_3548_);
v___x_3557_ = lean_nat_add(v___x_3556_, v_size_3547_);
lean_dec(v_size_3547_);
lean_dec(v___x_3556_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_impl_3545_);
lean_ctor_set(v___x_3057_, 0, v___x_3557_);
v___x_3559_ = v___x_3057_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_impl_3545_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3626_; 
lean_inc(v_l_3551_);
lean_inc(v_v_3550_);
lean_inc(v_k_3549_);
lean_inc(v_size_3548_);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; 
v_unused_3627_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_l_3054_, 2);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_l_3054_, 1);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3631_);
v___x_3562_ = v_l_3054_;
v_isShared_3563_ = v_isSharedCheck_3626_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v_l_3054_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3626_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_size_3564_; lean_object* v_size_3565_; lean_object* v_k_3566_; lean_object* v_v_3567_; lean_object* v_l_3568_; lean_object* v_r_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v_size_3564_ = lean_ctor_get(v_l_3551_, 0);
v_size_3565_ = lean_ctor_get(v_r_3552_, 0);
v_k_3566_ = lean_ctor_get(v_r_3552_, 1);
v_v_3567_ = lean_ctor_get(v_r_3552_, 2);
v_l_3568_ = lean_ctor_get(v_r_3552_, 3);
v_r_3569_ = lean_ctor_get(v_r_3552_, 4);
v___x_3570_ = lean_unsigned_to_nat(2u);
v___x_3571_ = lean_nat_mul(v___x_3570_, v_size_3564_);
v___x_3572_ = lean_nat_dec_lt(v_size_3565_, v___x_3571_);
lean_dec(v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3601_; 
lean_inc(v_r_3569_);
lean_inc(v_l_3568_);
lean_inc(v_v_3567_);
lean_inc(v_k_3566_);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_r_3552_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; 
v_unused_3602_ = lean_ctor_get(v_r_3552_, 4);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_r_3552_, 3);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_r_3552_, 2);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_r_3552_, 1);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_r_3552_, 0);
lean_dec(v_unused_3606_);
v___x_3574_ = v_r_3552_;
v_isShared_3575_ = v_isSharedCheck_3601_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v_r_3552_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3601_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___x_3589_; lean_object* v___y_3591_; 
v___x_3576_ = lean_nat_add(v___x_3546_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3577_ = lean_nat_add(v___x_3576_, v_size_3547_);
lean_dec(v___x_3576_);
v___x_3589_ = lean_nat_add(v___x_3546_, v_size_3564_);
if (lean_obj_tag(v_l_3568_) == 0)
{
lean_object* v_size_3599_; 
v_size_3599_ = lean_ctor_get(v_l_3568_, 0);
lean_inc(v_size_3599_);
v___y_3591_ = v_size_3599_;
goto v___jp_3590_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v___y_3591_ = v___x_3600_;
goto v___jp_3590_;
}
v___jp_3578_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_nat_add(v___y_3579_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec(v___y_3579_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 4, v_impl_3545_);
lean_ctor_set(v___x_3574_, 3, v_r_3569_);
lean_ctor_set(v___x_3574_, 2, v_v_3053_);
lean_ctor_set(v___x_3574_, 1, v_k_3052_);
lean_ctor_set(v___x_3574_, 0, v___x_3582_);
v___x_3584_ = v___x_3574_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_r_3569_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_impl_3545_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 4, v___x_3584_);
lean_ctor_set(v___x_3562_, 3, v___y_3580_);
lean_ctor_set(v___x_3562_, 2, v_v_3567_);
lean_ctor_set(v___x_3562_, 1, v_k_3566_);
lean_ctor_set(v___x_3562_, 0, v___x_3577_);
v___x_3586_ = v___x_3562_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3566_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3567_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v___y_3580_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
v___jp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = lean_nat_add(v___x_3589_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec(v___x_3589_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_l_3568_);
lean_ctor_set(v___x_3057_, 3, v_l_3551_);
lean_ctor_set(v___x_3057_, 2, v_v_3550_);
lean_ctor_set(v___x_3057_, 1, v_k_3549_);
lean_ctor_set(v___x_3057_, 0, v___x_3592_);
v___x_3594_ = v___x_3057_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_l_3551_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_l_3568_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_nat_add(v___x_3546_, v_size_3547_);
lean_dec(v_size_3547_);
if (lean_obj_tag(v_r_3569_) == 0)
{
lean_object* v_size_3596_; 
v_size_3596_ = lean_ctor_get(v_r_3569_, 0);
lean_inc(v_size_3596_);
v___y_3579_ = v___x_3595_;
v___y_3580_ = v___x_3594_;
v___y_3581_ = v_size_3596_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_unsigned_to_nat(0u);
v___y_3579_ = v___x_3595_;
v___y_3580_ = v___x_3594_;
v___y_3581_ = v___x_3597_;
goto v___jp_3578_;
}
}
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_del_object(v___x_3057_);
v___x_3607_ = lean_nat_add(v___x_3546_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3608_ = lean_nat_add(v___x_3607_, v_size_3547_);
lean_dec(v___x_3607_);
v___x_3609_ = lean_nat_add(v___x_3546_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3610_ = lean_nat_add(v___x_3609_, v_size_3565_);
lean_dec(v___x_3609_);
lean_inc_ref(v_impl_3545_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 4, v_impl_3545_);
lean_ctor_set(v___x_3562_, 3, v_r_3552_);
lean_ctor_set(v___x_3562_, 2, v_v_3053_);
lean_ctor_set(v___x_3562_, 1, v_k_3052_);
lean_ctor_set(v___x_3562_, 0, v___x_3610_);
v___x_3612_ = v___x_3562_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_impl_3545_);
v___x_3612_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v_isSharedCheck_3619_ = !lean_is_exclusive(v_impl_3545_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; lean_object* v_unused_3624_; 
v_unused_3620_ = lean_ctor_get(v_impl_3545_, 4);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_impl_3545_, 3);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_impl_3545_, 2);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_impl_3545_, 1);
lean_dec(v_unused_3623_);
v_unused_3624_ = lean_ctor_get(v_impl_3545_, 0);
lean_dec(v_unused_3624_);
v___x_3614_ = v_impl_3545_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v_impl_3545_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 4, v___x_3612_);
lean_ctor_set(v___x_3614_, 3, v_l_3551_);
lean_ctor_set(v___x_3614_, 2, v_v_3550_);
lean_ctor_set(v___x_3614_, 1, v_k_3549_);
lean_ctor_set(v___x_3614_, 0, v___x_3608_);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_l_3551_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v___x_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v_size_3632_ = lean_ctor_get(v_impl_3545_, 0);
lean_inc(v_size_3632_);
v___x_3633_ = lean_nat_add(v___x_3546_, v_size_3632_);
lean_dec(v_size_3632_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_impl_3545_);
lean_ctor_set(v___x_3057_, 0, v___x_3633_);
v___x_3635_ = v___x_3057_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_impl_3545_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
if (lean_obj_tag(v_l_3054_) == 0)
{
lean_object* v_l_3637_; 
v_l_3637_ = lean_ctor_get(v_l_3054_, 3);
if (lean_obj_tag(v_l_3637_) == 0)
{
lean_object* v_r_3638_; 
lean_inc_ref(v_l_3637_);
v_r_3638_ = lean_ctor_get(v_l_3054_, 4);
lean_inc(v_r_3638_);
if (lean_obj_tag(v_r_3638_) == 0)
{
lean_object* v_size_3639_; lean_object* v_k_3640_; lean_object* v_v_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3654_; 
v_size_3639_ = lean_ctor_get(v_l_3054_, 0);
v_k_3640_ = lean_ctor_get(v_l_3054_, 1);
v_v_3641_ = lean_ctor_get(v_l_3054_, 2);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; lean_object* v_unused_3656_; 
v_unused_3655_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3655_);
v_unused_3656_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3656_);
v___x_3643_ = v_l_3054_;
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_v_3641_);
lean_inc(v_k_3640_);
lean_inc(v_size_3639_);
lean_dec(v_l_3054_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v_size_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v_size_3645_ = lean_ctor_get(v_r_3638_, 0);
v___x_3646_ = lean_nat_add(v___x_3546_, v_size_3639_);
lean_dec(v_size_3639_);
v___x_3647_ = lean_nat_add(v___x_3546_, v_size_3645_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 4, v_impl_3545_);
lean_ctor_set(v___x_3643_, 3, v_r_3638_);
lean_ctor_set(v___x_3643_, 2, v_v_3053_);
lean_ctor_set(v___x_3643_, 1, v_k_3052_);
lean_ctor_set(v___x_3643_, 0, v___x_3647_);
v___x_3649_ = v___x_3643_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_r_3638_);
lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_impl_3545_);
v___x_3649_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3651_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v___x_3649_);
lean_ctor_set(v___x_3057_, 3, v_l_3637_);
lean_ctor_set(v___x_3057_, 2, v_v_3641_);
lean_ctor_set(v___x_3057_, 1, v_k_3640_);
lean_ctor_set(v___x_3057_, 0, v___x_3646_);
v___x_3651_ = v___x_3057_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3640_);
lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3641_);
lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_l_3637_);
lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_k_3657_; lean_object* v_v_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3669_; 
v_k_3657_ = lean_ctor_get(v_l_3054_, 1);
v_v_3658_ = lean_ctor_get(v_l_3054_, 2);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; lean_object* v_unused_3671_; lean_object* v_unused_3672_; 
v_unused_3670_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3672_);
v___x_3660_ = v_l_3054_;
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_v_3658_);
lean_inc(v_k_3657_);
lean_dec(v_l_3054_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3664_; 
v___x_3662_ = lean_unsigned_to_nat(3u);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 3, v_r_3638_);
lean_ctor_set(v___x_3660_, 2, v_v_3053_);
lean_ctor_set(v___x_3660_, 1, v_k_3052_);
lean_ctor_set(v___x_3660_, 0, v___x_3546_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_r_3638_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_r_3638_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v___x_3664_);
lean_ctor_set(v___x_3057_, 3, v_l_3637_);
lean_ctor_set(v___x_3057_, 2, v_v_3658_);
lean_ctor_set(v___x_3057_, 1, v_k_3657_);
lean_ctor_set(v___x_3057_, 0, v___x_3662_);
v___x_3666_ = v___x_3057_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3657_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3658_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_l_3637_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
else
{
lean_object* v_r_3673_; 
v_r_3673_ = lean_ctor_get(v_l_3054_, 4);
lean_inc(v_r_3673_);
if (lean_obj_tag(v_r_3673_) == 0)
{
lean_object* v_k_3674_; lean_object* v_v_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3698_; 
lean_inc(v_l_3637_);
v_k_3674_ = lean_ctor_get(v_l_3054_, 1);
v_v_3675_ = lean_ctor_get(v_l_3054_, 2);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_l_3054_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; lean_object* v_unused_3700_; lean_object* v_unused_3701_; 
v_unused_3699_ = lean_ctor_get(v_l_3054_, 4);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_l_3054_, 3);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_l_3054_, 0);
lean_dec(v_unused_3701_);
v___x_3677_ = v_l_3054_;
v_isShared_3678_ = v_isSharedCheck_3698_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_v_3675_);
lean_inc(v_k_3674_);
lean_dec(v_l_3054_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3698_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v_k_3679_; lean_object* v_v_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3694_; 
v_k_3679_ = lean_ctor_get(v_r_3673_, 1);
v_v_3680_ = lean_ctor_get(v_r_3673_, 2);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_r_3673_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; 
v_unused_3695_ = lean_ctor_get(v_r_3673_, 4);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_r_3673_, 3);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_r_3673_, 0);
lean_dec(v_unused_3697_);
v___x_3682_ = v_r_3673_;
v_isShared_3683_ = v_isSharedCheck_3694_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_v_3680_);
lean_inc(v_k_3679_);
lean_dec(v_r_3673_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3694_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(3u);
if (v_isShared_3683_ == 0)
{
lean_ctor_set(v___x_3682_, 4, v_l_3637_);
lean_ctor_set(v___x_3682_, 3, v_l_3637_);
lean_ctor_set(v___x_3682_, 2, v_v_3675_);
lean_ctor_set(v___x_3682_, 1, v_k_3674_);
lean_ctor_set(v___x_3682_, 0, v___x_3546_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_k_3674_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_v_3675_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v_l_3637_);
lean_ctor_set(v_reuseFailAlloc_3693_, 4, v_l_3637_);
v___x_3686_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3688_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_l_3637_);
lean_ctor_set(v___x_3677_, 2, v_v_3053_);
lean_ctor_set(v___x_3677_, 1, v_k_3052_);
lean_ctor_set(v___x_3677_, 0, v___x_3546_);
v___x_3688_ = v___x_3677_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v_l_3637_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v_l_3637_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v___x_3688_);
lean_ctor_set(v___x_3057_, 3, v___x_3686_);
lean_ctor_set(v___x_3057_, 2, v_v_3680_);
lean_ctor_set(v___x_3057_, 1, v_k_3679_);
lean_ctor_set(v___x_3057_, 0, v___x_3684_);
v___x_3690_ = v___x_3057_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
}
}
else
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
v___x_3702_ = lean_unsigned_to_nat(2u);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_r_3673_);
lean_ctor_set(v___x_3057_, 0, v___x_3702_);
v___x_3704_ = v___x_3057_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_r_3673_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v___x_3707_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 4, v_l_3054_);
lean_ctor_set(v___x_3057_, 0, v___x_3546_);
v___x_3707_ = v___x_3057_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_k_3052_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_v_3053_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v_l_3054_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v_l_3054_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
}
}
}
else
{
return v_t_3051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3711_, lean_object* v_t_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3711_, v_t_3712_);
lean_dec(v_k_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3714_, lean_object* v_x_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3714_, v_x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3717_, lean_object* v_x_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3717_, v_x_3718_);
lean_dec(v_declName_3717_);
return v_res_3719_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v___x_3731_; lean_object* v_env_3732_; lean_object* v___f_3733_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___x_3777_; 
v___x_3731_ = lean_st_ref_get(v___y_3729_);
v_env_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc_ref(v_env_3732_);
lean_dec(v___x_3731_);
lean_inc(v_declName_3723_);
v___f_3733_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3733_, 0, v_declName_3723_);
v___x_3777_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3732_, v_declName_3723_);
lean_dec_ref(v_env_3732_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec(v_declName_3723_);
v___y_3735_ = v___y_3727_;
v___y_3736_ = v___y_3729_;
goto v___jp_3734_;
}
else
{
uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec_ref(v___x_3777_);
lean_dec_ref(v___f_3733_);
v___x_3778_ = 0;
v___x_3779_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3780_ = l_Lean_MessageData_ofConstName(v_declName_3723_, v___x_3778_);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3781_);
lean_ctor_set(v___x_3783_, 1, v___x_3782_);
v___x_3784_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3783_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
return v___x_3784_;
}
v___jp_3734_:
{
lean_object* v___x_3737_; lean_object* v_env_3738_; lean_object* v_nextMacroScope_3739_; lean_object* v_ngen_3740_; lean_object* v_auxDeclNGen_3741_; lean_object* v_traceState_3742_; lean_object* v_messages_3743_; lean_object* v_infoState_3744_; lean_object* v_snapshotTasks_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3775_; 
v___x_3737_ = lean_st_ref_take(v___y_3736_);
v_env_3738_ = lean_ctor_get(v___x_3737_, 0);
v_nextMacroScope_3739_ = lean_ctor_get(v___x_3737_, 1);
v_ngen_3740_ = lean_ctor_get(v___x_3737_, 2);
v_auxDeclNGen_3741_ = lean_ctor_get(v___x_3737_, 3);
v_traceState_3742_ = lean_ctor_get(v___x_3737_, 4);
v_messages_3743_ = lean_ctor_get(v___x_3737_, 6);
v_infoState_3744_ = lean_ctor_get(v___x_3737_, 7);
v_snapshotTasks_3745_ = lean_ctor_get(v___x_3737_, 8);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; 
v_unused_3776_ = lean_ctor_get(v___x_3737_, 5);
lean_dec(v_unused_3776_);
v___x_3747_ = v___x_3737_;
v_isShared_3748_ = v_isSharedCheck_3775_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_snapshotTasks_3745_);
lean_inc(v_infoState_3744_);
lean_inc(v_messages_3743_);
lean_inc(v_traceState_3742_);
lean_inc(v_auxDeclNGen_3741_);
lean_inc(v_ngen_3740_);
lean_inc(v_nextMacroScope_3739_);
lean_inc(v_env_3738_);
lean_dec(v___x_3737_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3775_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3749_ = l_Lean_docStringExt;
v___x_3750_ = lean_box(2);
v___x_3751_ = lean_box(0);
v___x_3752_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3749_, v_env_3738_, v___f_3733_, v___x_3750_, v___x_3751_);
v___x_3753_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 5, v___x_3753_);
lean_ctor_set(v___x_3747_, 0, v___x_3752_);
v___x_3755_ = v___x_3747_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3752_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_nextMacroScope_3739_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_ngen_3740_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_auxDeclNGen_3741_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_traceState_3742_);
lean_ctor_set(v_reuseFailAlloc_3774_, 5, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3774_, 6, v_messages_3743_);
lean_ctor_set(v_reuseFailAlloc_3774_, 7, v_infoState_3744_);
lean_ctor_set(v_reuseFailAlloc_3774_, 8, v_snapshotTasks_3745_);
v___x_3755_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v_mctx_3758_; lean_object* v_zetaDeltaFVarIds_3759_; lean_object* v_postponed_3760_; lean_object* v_diag_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3772_; 
v___x_3756_ = lean_st_ref_set(v___y_3736_, v___x_3755_);
v___x_3757_ = lean_st_ref_take(v___y_3735_);
v_mctx_3758_ = lean_ctor_get(v___x_3757_, 0);
v_zetaDeltaFVarIds_3759_ = lean_ctor_get(v___x_3757_, 2);
v_postponed_3760_ = lean_ctor_get(v___x_3757_, 3);
v_diag_3761_ = lean_ctor_get(v___x_3757_, 4);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; 
v_unused_3773_ = lean_ctor_get(v___x_3757_, 1);
lean_dec(v_unused_3773_);
v___x_3763_ = v___x_3757_;
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_diag_3761_);
lean_inc(v_postponed_3760_);
lean_inc(v_zetaDeltaFVarIds_3759_);
lean_inc(v_mctx_3758_);
lean_dec(v___x_3757_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3772_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
v___x_3765_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3765_);
v___x_3767_ = v___x_3763_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_mctx_3758_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_zetaDeltaFVarIds_3759_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_postponed_3760_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_diag_3761_);
v___x_3767_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_st_ref_set(v___y_3735_, v___x_3767_);
v___x_3769_ = lean_box(0);
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
return v___x_3770_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
return v_res_3793_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3796_ = l_Lean_stringToMessageData(v___x_3795_);
return v___x_3796_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3799_ = l_Lean_stringToMessageData(v___x_3798_);
return v___x_3799_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3802_ = l_Lean_stringToMessageData(v___x_3801_);
return v___x_3802_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3805_ = l_Lean_stringToMessageData(v___x_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v_env_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; 
v___x_3814_ = lean_st_ref_get(v_a_3812_);
v_env_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc_ref(v_env_3815_);
lean_dec(v___x_3814_);
v___x_3816_ = 1;
lean_inc(v_declName_3806_);
v___x_3817_ = l_Lean_findInternalDocString_x3f(v_env_3815_, v_declName_3806_, v___x_3816_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3817_);
if (lean_obj_tag(v_a_3818_) == 1)
{
lean_object* v_val_3819_; 
v_val_3819_ = lean_ctor_get(v_a_3818_, 0);
lean_inc(v_val_3819_);
lean_dec_ref(v_a_3818_);
if (lean_obj_tag(v_val_3819_) == 0)
{
lean_object* v_val_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3842_; 
v_val_3820_ = lean_ctor_get(v_val_3819_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_val_3819_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3822_ = v_val_3819_;
v_isShared_3823_ = v_isSharedCheck_3842_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_val_3820_);
lean_dec(v_val_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3842_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_removeBuiltinDocString(v_declName_3806_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref(v___x_3824_);
lean_del_object(v___x_3822_);
lean_inc(v_declName_3806_);
v___x_3825_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v___x_3826_; 
lean_dec_ref(v___x_3825_);
v___x_3826_ = l_Lean_addVersoDocStringFromString(v_declName_3806_, v_val_3820_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
return v___x_3826_;
}
else
{
lean_dec(v_val_3820_);
lean_dec(v_declName_3806_);
return v___x_3825_;
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_val_3820_);
lean_dec(v_declName_3806_);
v_a_3827_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3829_ = v___x_3824_;
v_isShared_3830_ = v_isSharedCheck_3841_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3824_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3841_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_ref_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v_ref_3831_ = lean_ctor_get(v_a_3811_, 5);
v___x_3832_ = lean_io_error_to_string(v_a_3827_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 3);
lean_ctor_set(v___x_3822_, 0, v___x_3832_);
v___x_3834_ = v___x_3822_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3835_ = l_Lean_MessageData_ofFormat(v___x_3834_);
lean_inc(v_ref_3831_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v_ref_3831_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 0, v___x_3836_);
v___x_3838_ = v___x_3829_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
}
else
{
lean_object* v___x_3843_; uint8_t v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec(v_val_3819_);
v___x_3843_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3844_ = 0;
v___x_3845_ = l_Lean_MessageData_ofConstName(v_declName_3806_, v___x_3844_);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3843_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3848_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
return v___x_3849_;
}
}
else
{
lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec(v_a_3818_);
v___x_3850_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3851_ = 0;
v___x_3852_ = l_Lean_MessageData_ofConstName(v_declName_3806_, v___x_3851_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3850_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3855_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_);
return v___x_3856_;
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_declName_3806_);
v_a_3857_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3859_ = v___x_3817_;
v_isShared_3860_ = v_isSharedCheck_3869_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3817_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3869_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v_ref_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3867_; 
v_ref_3861_ = lean_ctor_get(v_a_3811_, 5);
v___x_3862_ = lean_io_error_to_string(v_a_3857_);
v___x_3863_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3862_);
v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
lean_inc(v_ref_3861_);
v___x_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3865_, 0, v_ref_3861_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3865_);
v___x_3867_ = v___x_3859_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_makeDocStringVerso(v_declName_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
lean_dec_ref(v_a_3873_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3879_, lean_object* v_k_3880_, lean_object* v_t_3881_, lean_object* v_h_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3880_, v_t_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3884_, lean_object* v_k_3885_, lean_object* v_t_3886_, lean_object* v_h_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3884_, v_k_3885_, v_t_3886_, v_h_3887_);
lean_dec(v_k_3885_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3889_, lean_object* v_binders_3890_, lean_object* v_docComment_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_options_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; lean_object* v___x_3902_; 
v_options_3899_ = lean_ctor_get(v_a_3896_, 2);
v___x_3900_ = l_Lean_doc_verso;
v___x_3901_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__5_spec__6(v_options_3899_, v___x_3900_);
v___x_3902_ = l_Lean_addDocStringOf(v___x_3901_, v_declName_3889_, v_binders_3890_, v_docComment_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3903_, lean_object* v_binders_3904_, lean_object* v_docComment_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_addDocString(v_declName_3903_, v_binders_3904_, v_docComment_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec_ref(v_a_3908_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3914_, lean_object* v_binders_3915_, lean_object* v_docString_x3f_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3916_) == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec(v_binders_3915_);
lean_dec(v_declName_3914_);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v_val_3926_; lean_object* v___x_3927_; 
v_val_3926_ = lean_ctor_get(v_docString_x3f_3916_, 0);
lean_inc(v_val_3926_);
lean_dec_ref(v_docString_x3f_3916_);
v___x_3927_ = l_Lean_addDocString(v_declName_3914_, v_binders_3915_, v_val_3926_, v_a_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
return v___x_3927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3928_, lean_object* v_binders_3929_, lean_object* v_docString_x3f_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_addDocString_x27(v_declName_3928_, v_binders_3929_, v_docString_x3f_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; lean_object* v_nextMacroScope_3944_; lean_object* v_ngen_3945_; lean_object* v_auxDeclNGen_3946_; lean_object* v_traceState_3947_; lean_object* v_messages_3948_; lean_object* v_infoState_3949_; lean_object* v_snapshotTasks_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3976_; 
v___x_3943_ = lean_st_ref_take(v___y_3941_);
v_nextMacroScope_3944_ = lean_ctor_get(v___x_3943_, 1);
v_ngen_3945_ = lean_ctor_get(v___x_3943_, 2);
v_auxDeclNGen_3946_ = lean_ctor_get(v___x_3943_, 3);
v_traceState_3947_ = lean_ctor_get(v___x_3943_, 4);
v_messages_3948_ = lean_ctor_get(v___x_3943_, 6);
v_infoState_3949_ = lean_ctor_get(v___x_3943_, 7);
v_snapshotTasks_3950_ = lean_ctor_get(v___x_3943_, 8);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; lean_object* v_unused_3978_; 
v_unused_3977_ = lean_ctor_get(v___x_3943_, 5);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v___x_3943_, 0);
lean_dec(v_unused_3978_);
v___x_3952_ = v___x_3943_;
v_isShared_3953_ = v_isSharedCheck_3976_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_snapshotTasks_3950_);
lean_inc(v_infoState_3949_);
lean_inc(v_messages_3948_);
lean_inc(v_traceState_3947_);
lean_inc(v_auxDeclNGen_3946_);
lean_inc(v_ngen_3945_);
lean_inc(v_nextMacroScope_3944_);
lean_dec(v___x_3943_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3976_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3956_; 
v___x_3954_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 5, v___x_3954_);
lean_ctor_set(v___x_3952_, 0, v_env_3939_);
v___x_3956_ = v___x_3952_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_env_3939_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v_nextMacroScope_3944_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v_ngen_3945_);
lean_ctor_set(v_reuseFailAlloc_3975_, 3, v_auxDeclNGen_3946_);
lean_ctor_set(v_reuseFailAlloc_3975_, 4, v_traceState_3947_);
lean_ctor_set(v_reuseFailAlloc_3975_, 5, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3975_, 6, v_messages_3948_);
lean_ctor_set(v_reuseFailAlloc_3975_, 7, v_infoState_3949_);
lean_ctor_set(v_reuseFailAlloc_3975_, 8, v_snapshotTasks_3950_);
v___x_3956_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v_mctx_3959_; lean_object* v_zetaDeltaFVarIds_3960_; lean_object* v_postponed_3961_; lean_object* v_diag_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3973_; 
v___x_3957_ = lean_st_ref_set(v___y_3941_, v___x_3956_);
v___x_3958_ = lean_st_ref_take(v___y_3940_);
v_mctx_3959_ = lean_ctor_get(v___x_3958_, 0);
v_zetaDeltaFVarIds_3960_ = lean_ctor_get(v___x_3958_, 2);
v_postponed_3961_ = lean_ctor_get(v___x_3958_, 3);
v_diag_3962_ = lean_ctor_get(v___x_3958_, 4);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; 
v_unused_3974_ = lean_ctor_get(v___x_3958_, 1);
lean_dec(v_unused_3974_);
v___x_3964_ = v___x_3958_;
v_isShared_3965_ = v_isSharedCheck_3973_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_diag_3962_);
lean_inc(v_postponed_3961_);
lean_inc(v_zetaDeltaFVarIds_3960_);
lean_inc(v_mctx_3959_);
lean_dec(v___x_3958_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3973_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3966_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 1, v___x_3966_);
v___x_3968_ = v___x_3964_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_mctx_3959_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3972_, 2, v_zetaDeltaFVarIds_3960_);
lean_ctor_set(v_reuseFailAlloc_3972_, 3, v_postponed_3961_);
lean_ctor_set(v_reuseFailAlloc_3972_, 4, v_diag_3962_);
v___x_3968_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = lean_st_ref_set(v___y_3940_, v___x_3968_);
v___x_3970_ = lean_box(0);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
return v___x_3971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec(v___y_3980_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v_env_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3992_ = lean_st_ref_get(v___y_3990_);
v_env_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc_ref(v_env_3993_);
lean_dec(v___x_3992_);
v___x_3994_ = l_Lean_getMainModuleDoc(v_env_3993_);
v___x_3995_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3994_);
lean_dec_ref(v___x_3994_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_dec_ref(v_docs_3984_);
v___x_3996_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_3997_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3996_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; lean_object* v_env_3999_; lean_object* v___x_4000_; 
v___x_3998_ = lean_st_ref_get(v___y_3990_);
v_env_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc_ref(v_env_3999_);
lean_dec(v___x_3998_);
v___x_4000_ = l_Lean_addVersoModuleDocSnippet(v_env_3999_, v_docs_3984_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v___x_4002_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_4003_ = l_Lean_stringToMessageData(v_a_4001_);
v___x_4004_ = l_Lean_indentD(v___x_4003_);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4002_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4005_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
return v___x_4006_;
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4008_; 
v_a_4007_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4007_);
lean_dec_ref(v___x_4000_);
v___x_4008_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4007_, v___y_3988_, v___y_3990_);
return v___x_4008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4018_, lean_object* v_docComment_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_versoModDocString(v_range_4018_, v_docComment_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref(v___x_4027_);
v___x_4029_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_a_4028_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_);
return v___x_4029_;
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v_a_4030_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4027_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4027_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4038_, lean_object* v_docComment_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_addVersoModDocString(v_range_4038_, v_docComment_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_docComment_4039_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4048_, v___y_4052_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4065_;
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
