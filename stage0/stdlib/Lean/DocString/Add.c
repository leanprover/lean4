// Lean compiler output
// Module: Lean.DocString.Add
// Imports: import Lean.Elab.DocString public import Lean.DocString.DeferredCheck public import Lean.DocString.Parser public import Lean.Elab.Term.TermElabM
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Doc_deferredCheckExt;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_Core_getAndEmptyMessageLog___redArg(lean_object*);
lean_object* l_Lean_Core_setMessageLog___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_exec___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_toArray(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
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
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__2___closed__1_value;
static const lean_string_object l_Lean_parseVersoDocString___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_parseVersoDocString___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_parseVersoDocString___redArg___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringOfText___closed__0 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__0_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringOfText___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_versoDocStringOfText___closed__1 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__1_value;
static const lean_closure_object l_Lean_versoDocStringOfText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__1_value)} };
static const lean_object* l_Lean_versoDocStringOfText___closed__2 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__2_value;
static const lean_array_object l_Lean_versoDocStringOfText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringOfText___closed__3 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__3_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value),((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__4 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__4_value;
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__4_value),((lean_object*)&l_Lean_versoDocStringOfText___closed__3_value)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__5 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_versoDocString___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_versoDocString___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__0_value_aux_0),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_versoDocString___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__0_value_aux_1),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__0_value_aux_2),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static const lean_string_object l_Lean_versoDocString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_versoDocString___closed__1 = (const lean_object*)&l_Lean_versoDocString___closed__1_value;
static const lean_string_object l_Lean_versoDocString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_versoDocString___closed__2 = (const lean_object*)&l_Lean_versoDocString___closed__2_value;
static const lean_string_object l_Lean_versoDocString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parseFailure"};
static const lean_object* l_Lean_versoDocString___closed__3 = (const lean_object*)&l_Lean_versoDocString___closed__3_value;
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_parseVersoDocString___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_0),((lean_object*)&l_Lean_versoDocString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_1),((lean_object*)&l_Lean_versoDocString___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_2),((lean_object*)&l_Lean_versoDocString___closed__3_value),LEAN_SCALAR_PTR_LITERAL(229, 162, 159, 121, 181, 7, 46, 32)}};
static const lean_object* l_Lean_versoDocString___closed__4 = (const lean_object*)&l_Lean_versoDocString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_versoDocStringFromString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_versoDocStringFromString___closed__0 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__0_value;
static const lean_string_object l_Lean_versoDocStringFromString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_versoDocStringFromString___closed__1 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__1_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__2 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__2_value;
static const lean_ctor_object l_Lean_versoDocStringFromString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringFromString___closed__2_value),((lean_object*)&l_Lean_versoDocStringFromString___closed__0_value)}};
static const lean_object* l_Lean_versoDocStringFromString___closed__3 = (const lean_object*)&l_Lean_versoDocStringFromString___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration '"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is in an imported module"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Error adding module docs: "};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "Can't add Verso-format module docs because there is already Markdown-format content present."};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_97_, 1);
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
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v_text_146_, lean_object* v_pos_147_, lean_object* v_source_148_, uint8_t v___x_149_, lean_object* v_logMessage_150_, lean_object* v_toBind_151_, lean_object* v___f_152_, lean_object* v_____do__lift_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint32_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_154_ = l_Lean_FileMap_toPosition(v_text_146_, v_pos_147_);
v___x_155_ = lean_box(0);
v___x_156_ = 2;
v___x_157_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
v___x_158_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__1));
v___x_159_ = lean_string_utf8_get(v_source_148_, v_pos_147_);
v___x_160_ = lean_string_push(v___x_157_, v___x_159_);
v___x_161_ = lean_string_append(v___x_158_, v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__2));
v___x_163_ = lean_string_append(v___x_161_, v___x_162_);
v___x_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = l_Lean_MessageData_ofFormat(v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_166_, 0, v_____do__lift_153_);
lean_ctor_set(v___x_166_, 1, v___x_154_);
lean_ctor_set(v___x_166_, 2, v___x_155_);
lean_ctor_set(v___x_166_, 3, v___x_157_);
lean_ctor_set(v___x_166_, 4, v___x_165_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5, v___x_149_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 1, v___x_156_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*5 + 2, v___x_149_);
v___x_167_ = lean_apply_1(v_logMessage_150_, v___x_166_);
v___x_168_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_167_, v___f_152_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2___boxed(lean_object* v_text_169_, lean_object* v_pos_170_, lean_object* v_source_171_, lean_object* v___x_172_, lean_object* v_logMessage_173_, lean_object* v_toBind_174_, lean_object* v___f_175_, lean_object* v_____do__lift_176_){
_start:
{
uint8_t v___x_1657__boxed_177_; lean_object* v_res_178_; 
v___x_1657__boxed_177_ = lean_unbox(v___x_172_);
v_res_178_ = l_Lean_parseVersoDocString___redArg___lam__2(v_text_169_, v_pos_170_, v_source_171_, v___x_1657__boxed_177_, v_logMessage_173_, v_toBind_174_, v___f_175_, v_____do__lift_176_);
lean_dec_ref(v_source_171_);
lean_dec(v_pos_170_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_toApplicative_179_, lean_object* v___x_180_, lean_object* v_____r_181_){
_start:
{
lean_object* v_toPure_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_toPure_182_ = lean_ctor_get(v_toApplicative_179_, 1);
lean_inc(v_toPure_182_);
lean_dec_ref(v_toApplicative_179_);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_180_);
v___x_184_ = lean_apply_2(v_toPure_182_, lean_box(0), v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_185_, lean_object* v_fst_186_, lean_object* v_snd_187_, lean_object* v_logMessage_188_, lean_object* v_toBind_189_, lean_object* v___f_190_, lean_object* v_____do__lift_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_192_ = l_Lean_FileMap_toPosition(v_text_185_, v_fst_186_);
v___x_193_ = lean_box(0);
v___x_194_ = 0;
v___x_195_ = 2;
v___x_196_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
v___x_197_ = l_Lean_Parser_Error_toString(v_snd_187_);
v___x_198_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = l_Lean_MessageData_ofFormat(v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_200_, 0, v_____do__lift_191_);
lean_ctor_set(v___x_200_, 1, v___x_192_);
lean_ctor_set(v___x_200_, 2, v___x_193_);
lean_ctor_set(v___x_200_, 3, v___x_196_);
lean_ctor_set(v___x_200_, 4, v___x_199_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*5, v___x_194_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*5 + 1, v___x_195_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*5 + 2, v___x_194_);
v___x_201_ = lean_apply_1(v_logMessage_188_, v___x_200_);
v___x_202_ = lean_apply_4(v_toBind_189_, lean_box(0), lean_box(0), v___x_201_, v___f_190_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_203_, lean_object* v_fst_204_, lean_object* v_snd_205_, lean_object* v_logMessage_206_, lean_object* v_toBind_207_, lean_object* v___f_208_, lean_object* v_____do__lift_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_203_, v_fst_204_, v_snd_205_, v_logMessage_206_, v_toBind_207_, v___f_208_, v_____do__lift_209_);
lean_dec(v_fst_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_text_211_, lean_object* v_logMessage_212_, lean_object* v_toBind_213_, lean_object* v___f_214_, lean_object* v_getFileName_215_, lean_object* v_a_216_, lean_object* v_x_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_snd_219_; lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___f_222_; lean_object* v___x_223_; 
v_snd_219_ = lean_ctor_get(v_a_216_, 1);
lean_inc(v_snd_219_);
v_fst_220_ = lean_ctor_get(v_a_216_, 0);
lean_inc(v_fst_220_);
lean_dec_ref(v_a_216_);
v_snd_221_ = lean_ctor_get(v_snd_219_, 1);
lean_inc(v_snd_221_);
lean_dec(v_snd_219_);
lean_inc(v_toBind_213_);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_222_, 0, v_text_211_);
lean_closure_set(v___f_222_, 1, v_fst_220_);
lean_closure_set(v___f_222_, 2, v_snd_221_);
lean_closure_set(v___f_222_, 3, v_logMessage_212_);
lean_closure_set(v___f_222_, 4, v_toBind_213_);
lean_closure_set(v___f_222_, 5, v___f_214_);
v___x_223_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v_getFileName_215_, v___f_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_ictx_224_, lean_object* v_toApplicative_225_, lean_object* v_text_226_, lean_object* v_source_227_, lean_object* v_logMessage_228_, lean_object* v_toBind_229_, lean_object* v___f_230_, lean_object* v_getFileName_231_, lean_object* v_inst_232_, lean_object* v___f_233_, lean_object* v_env_234_, lean_object* v_____do__lift_235_, lean_object* v_____do__lift_236_, lean_object* v_val_237_, lean_object* v___y_238_, lean_object* v___x_239_, lean_object* v_____do__lift_240_){
_start:
{
lean_object* v___y_242_; lean_object* v_pmctx_266_; lean_object* v_blockCtxt_267_; lean_object* v___x_268_; lean_object* v_s_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_s_272_; uint8_t v___y_274_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
lean_inc_ref(v_env_234_);
v_pmctx_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_266_, 0, v_env_234_);
lean_ctor_set(v_pmctx_266_, 1, v_____do__lift_235_);
lean_ctor_set(v_pmctx_266_, 2, v_____do__lift_236_);
lean_ctor_set(v_pmctx_266_, 3, v_____do__lift_240_);
lean_inc(v_val_237_);
lean_inc_ref(v_text_226_);
v_blockCtxt_267_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_226_, v_val_237_, v___y_238_);
v___x_268_ = l_Lean_Parser_mkParserState(v_source_227_);
lean_inc_ref(v___x_268_);
v_s_269_ = l_Lean_Parser_ParserState_setPos(v___x_268_, v_val_237_);
v___x_270_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_270_, 0, v_blockCtxt_267_);
v___x_271_ = l_Lean_Parser_getTokenTable(v_env_234_);
lean_inc_ref(v___x_271_);
lean_inc_ref(v_pmctx_266_);
lean_inc_ref(v_ictx_224_);
v_s_272_ = l_Lean_Parser_ParserFn_run(v___x_270_, v_ictx_224_, v_pmctx_266_, v___x_271_, v_s_269_);
lean_inc_ref(v_s_272_);
v___x_284_ = l_Lean_Parser_ParserState_allErrors(v_s_272_);
v___x_285_ = lean_array_get_size(v___x_284_);
lean_dec_ref(v___x_284_);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_nat_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
v___y_274_ = v___x_287_;
goto v___jp_273_;
}
else
{
lean_object* v_pos_288_; uint8_t v___x_289_; uint8_t v___x_290_; 
v_pos_288_ = lean_ctor_get(v_s_272_, 2);
lean_inc(v_pos_288_);
v___x_289_ = l_Lean_Parser_InputContext_atEnd(v_ictx_224_, v_pos_288_);
lean_dec(v_pos_288_);
v___x_290_ = lean_bool_not(v___x_289_);
v___y_274_ = v___x_290_;
goto v___jp_273_;
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; uint8_t v___x_247_; 
lean_inc_ref(v___y_242_);
v___x_243_ = l_Lean_Parser_ParserState_allErrors(v___y_242_);
v___x_244_ = lean_array_get_size(v___x_243_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_dec_eq(v___x_244_, v___x_245_);
v___x_247_ = lean_bool_not(v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v_stxStack_248_; lean_object* v_pos_249_; uint8_t v___x_250_; uint8_t v___x_251_; 
lean_dec_ref(v___x_243_);
lean_dec(v___f_233_);
lean_dec_ref(v_inst_232_);
v_stxStack_248_ = lean_ctor_get(v___y_242_, 0);
lean_inc_ref(v_stxStack_248_);
v_pos_249_ = lean_ctor_get(v___y_242_, 2);
lean_inc(v_pos_249_);
lean_dec_ref(v___y_242_);
v___x_250_ = l_Lean_Parser_InputContext_atEnd(v_ictx_224_, v_pos_249_);
lean_dec_ref(v_ictx_224_);
v___x_251_ = lean_bool_not(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v_toPure_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_pos_249_);
lean_dec(v_getFileName_231_);
lean_dec(v___f_230_);
lean_dec(v_toBind_229_);
lean_dec(v_logMessage_228_);
lean_dec_ref(v_source_227_);
lean_dec_ref(v_text_226_);
v_toPure_252_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_252_);
lean_dec_ref(v_toApplicative_225_);
v___x_253_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_248_);
lean_dec_ref(v_stxStack_248_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___x_255_ = lean_apply_2(v_toPure_252_, lean_box(0), v___x_254_);
return v___x_255_;
}
else
{
lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___x_258_; 
lean_dec_ref(v_stxStack_248_);
lean_dec_ref(v_toApplicative_225_);
v___x_256_ = lean_box(v___x_247_);
lean_inc(v_toBind_229_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_257_, 0, v_text_226_);
lean_closure_set(v___f_257_, 1, v_pos_249_);
lean_closure_set(v___f_257_, 2, v_source_227_);
lean_closure_set(v___f_257_, 3, v___x_256_);
lean_closure_set(v___f_257_, 4, v_logMessage_228_);
lean_closure_set(v___f_257_, 5, v_toBind_229_);
lean_closure_set(v___f_257_, 6, v___f_230_);
v___x_258_ = lean_apply_4(v_toBind_229_, lean_box(0), lean_box(0), v_getFileName_231_, v___f_257_);
return v___x_258_;
}
}
else
{
lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___f_261_; size_t v_sz_262_; size_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v___y_242_);
lean_dec(v___f_230_);
lean_dec_ref(v_source_227_);
lean_dec_ref(v_ictx_224_);
v___x_259_ = lean_box(0);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3), 3, 2);
lean_closure_set(v___f_260_, 0, v_toApplicative_225_);
lean_closure_set(v___f_260_, 1, v___x_259_);
lean_inc(v_toBind_229_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5), 8, 5);
lean_closure_set(v___f_261_, 0, v_text_226_);
lean_closure_set(v___f_261_, 1, v_logMessage_228_);
lean_closure_set(v___f_261_, 2, v_toBind_229_);
lean_closure_set(v___f_261_, 3, v___f_260_);
lean_closure_set(v___f_261_, 4, v_getFileName_231_);
v_sz_262_ = lean_array_size(v___x_243_);
v___x_263_ = ((size_t)0ULL);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_232_, v___x_243_, v___f_261_, v_sz_262_, v___x_263_, v___x_259_);
v___x_265_ = lean_apply_4(v_toBind_229_, lean_box(0), lean_box(0), v___x_264_, v___f_233_);
return v___x_265_;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
lean_dec_ref(v___x_271_);
lean_dec_ref(v___x_268_);
lean_dec_ref_known(v_pmctx_266_, 4);
lean_dec(v___x_239_);
v___y_242_ = v_s_272_;
goto v___jp_241_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_pos_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = lean_box(0);
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_239_);
lean_ctor_set(v___x_278_, 1, v___x_275_);
v___x_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_279_, 0, v___x_275_);
lean_ctor_set(v___x_279_, 1, v___x_276_);
lean_ctor_set(v___x_279_, 2, v___x_277_);
lean_ctor_set(v___x_279_, 3, v___x_278_);
lean_ctor_set(v___x_279_, 4, v___x_275_);
v_pos_280_ = lean_ctor_get(v_s_272_, 2);
lean_inc(v_pos_280_);
lean_dec_ref(v_s_272_);
v___x_281_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_281_, 0, v___x_279_);
v___x_282_ = l_Lean_Parser_ParserState_setPos(v___x_268_, v_pos_280_);
lean_inc_ref(v_ictx_224_);
v___x_283_ = l_Lean_Parser_ParserFn_run(v___x_281_, v_ictx_224_, v_pmctx_266_, v___x_271_, v___x_282_);
v___y_242_ = v___x_283_;
goto v___jp_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_ictx_291_ = _args[0];
lean_object* v_toApplicative_292_ = _args[1];
lean_object* v_text_293_ = _args[2];
lean_object* v_source_294_ = _args[3];
lean_object* v_logMessage_295_ = _args[4];
lean_object* v_toBind_296_ = _args[5];
lean_object* v___f_297_ = _args[6];
lean_object* v_getFileName_298_ = _args[7];
lean_object* v_inst_299_ = _args[8];
lean_object* v___f_300_ = _args[9];
lean_object* v_env_301_ = _args[10];
lean_object* v_____do__lift_302_ = _args[11];
lean_object* v_____do__lift_303_ = _args[12];
lean_object* v_val_304_ = _args[13];
lean_object* v___y_305_ = _args[14];
lean_object* v___x_306_ = _args[15];
lean_object* v_____do__lift_307_ = _args[16];
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_parseVersoDocString___redArg___lam__6(v_ictx_291_, v_toApplicative_292_, v_text_293_, v_source_294_, v_logMessage_295_, v_toBind_296_, v___f_297_, v_getFileName_298_, v_inst_299_, v___f_300_, v_env_301_, v_____do__lift_302_, v_____do__lift_303_, v_val_304_, v___y_305_, v___x_306_, v_____do__lift_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_ictx_309_, lean_object* v_toApplicative_310_, lean_object* v_text_311_, lean_object* v_source_312_, lean_object* v_logMessage_313_, lean_object* v_toBind_314_, lean_object* v___f_315_, lean_object* v_getFileName_316_, lean_object* v_inst_317_, lean_object* v___f_318_, lean_object* v_env_319_, lean_object* v_____do__lift_320_, lean_object* v_val_321_, lean_object* v___y_322_, lean_object* v___x_323_, lean_object* v_getOpenDecls_324_, lean_object* v_____do__lift_325_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; 
lean_inc(v_toBind_314_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_326_, 0, v_ictx_309_);
lean_closure_set(v___f_326_, 1, v_toApplicative_310_);
lean_closure_set(v___f_326_, 2, v_text_311_);
lean_closure_set(v___f_326_, 3, v_source_312_);
lean_closure_set(v___f_326_, 4, v_logMessage_313_);
lean_closure_set(v___f_326_, 5, v_toBind_314_);
lean_closure_set(v___f_326_, 6, v___f_315_);
lean_closure_set(v___f_326_, 7, v_getFileName_316_);
lean_closure_set(v___f_326_, 8, v_inst_317_);
lean_closure_set(v___f_326_, 9, v___f_318_);
lean_closure_set(v___f_326_, 10, v_env_319_);
lean_closure_set(v___f_326_, 11, v_____do__lift_320_);
lean_closure_set(v___f_326_, 12, v_____do__lift_325_);
lean_closure_set(v___f_326_, 13, v_val_321_);
lean_closure_set(v___f_326_, 14, v___y_322_);
lean_closure_set(v___f_326_, 15, v___x_323_);
v___x_327_ = lean_apply_4(v_toBind_314_, lean_box(0), lean_box(0), v_getOpenDecls_324_, v___f_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_ictx_328_ = _args[0];
lean_object* v_toApplicative_329_ = _args[1];
lean_object* v_text_330_ = _args[2];
lean_object* v_source_331_ = _args[3];
lean_object* v_logMessage_332_ = _args[4];
lean_object* v_toBind_333_ = _args[5];
lean_object* v___f_334_ = _args[6];
lean_object* v_getFileName_335_ = _args[7];
lean_object* v_inst_336_ = _args[8];
lean_object* v___f_337_ = _args[9];
lean_object* v_env_338_ = _args[10];
lean_object* v_____do__lift_339_ = _args[11];
lean_object* v_val_340_ = _args[12];
lean_object* v___y_341_ = _args[13];
lean_object* v___x_342_ = _args[14];
lean_object* v_getOpenDecls_343_ = _args[15];
lean_object* v_____do__lift_344_ = _args[16];
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_parseVersoDocString___redArg___lam__7(v_ictx_328_, v_toApplicative_329_, v_text_330_, v_source_331_, v_logMessage_332_, v_toBind_333_, v___f_334_, v_getFileName_335_, v_inst_336_, v___f_337_, v_env_338_, v_____do__lift_339_, v_val_340_, v___y_341_, v___x_342_, v_getOpenDecls_343_, v_____do__lift_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_inst_346_, lean_object* v_ictx_347_, lean_object* v_toApplicative_348_, lean_object* v_text_349_, lean_object* v_source_350_, lean_object* v_logMessage_351_, lean_object* v_toBind_352_, lean_object* v___f_353_, lean_object* v_getFileName_354_, lean_object* v_inst_355_, lean_object* v___f_356_, lean_object* v_env_357_, lean_object* v_val_358_, lean_object* v___y_359_, lean_object* v___x_360_, lean_object* v_____do__lift_361_){
_start:
{
lean_object* v_getCurrNamespace_362_; lean_object* v_getOpenDecls_363_; lean_object* v___f_364_; lean_object* v___x_365_; 
v_getCurrNamespace_362_ = lean_ctor_get(v_inst_346_, 0);
lean_inc(v_getCurrNamespace_362_);
v_getOpenDecls_363_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_getOpenDecls_363_);
lean_dec_ref(v_inst_346_);
lean_inc(v_toBind_352_);
v___f_364_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_364_, 0, v_ictx_347_);
lean_closure_set(v___f_364_, 1, v_toApplicative_348_);
lean_closure_set(v___f_364_, 2, v_text_349_);
lean_closure_set(v___f_364_, 3, v_source_350_);
lean_closure_set(v___f_364_, 4, v_logMessage_351_);
lean_closure_set(v___f_364_, 5, v_toBind_352_);
lean_closure_set(v___f_364_, 6, v___f_353_);
lean_closure_set(v___f_364_, 7, v_getFileName_354_);
lean_closure_set(v___f_364_, 8, v_inst_355_);
lean_closure_set(v___f_364_, 9, v___f_356_);
lean_closure_set(v___f_364_, 10, v_env_357_);
lean_closure_set(v___f_364_, 11, v_____do__lift_361_);
lean_closure_set(v___f_364_, 12, v_val_358_);
lean_closure_set(v___f_364_, 13, v___y_359_);
lean_closure_set(v___f_364_, 14, v___x_360_);
lean_closure_set(v___f_364_, 15, v_getOpenDecls_363_);
v___x_365_ = lean_apply_4(v_toBind_352_, lean_box(0), lean_box(0), v_getCurrNamespace_362_, v___f_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_source_366_, lean_object* v_text_367_, lean_object* v___y_368_, lean_object* v_inst_369_, lean_object* v_toApplicative_370_, lean_object* v_logMessage_371_, lean_object* v_toBind_372_, lean_object* v___f_373_, lean_object* v_getFileName_374_, lean_object* v_inst_375_, lean_object* v___f_376_, lean_object* v_env_377_, lean_object* v_val_378_, lean_object* v___x_379_, lean_object* v_inst_380_, lean_object* v_____do__lift_381_){
_start:
{
lean_object* v_ictx_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
lean_inc(v___y_368_);
lean_inc_ref(v_text_367_);
lean_inc_ref(v_source_366_);
v_ictx_382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_382_, 0, v_source_366_);
lean_ctor_set(v_ictx_382_, 1, v_____do__lift_381_);
lean_ctor_set(v_ictx_382_, 2, v_text_367_);
lean_ctor_set(v_ictx_382_, 3, v___y_368_);
lean_inc(v_toBind_372_);
v___f_383_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(v___f_383_, 0, v_inst_369_);
lean_closure_set(v___f_383_, 1, v_ictx_382_);
lean_closure_set(v___f_383_, 2, v_toApplicative_370_);
lean_closure_set(v___f_383_, 3, v_text_367_);
lean_closure_set(v___f_383_, 4, v_source_366_);
lean_closure_set(v___f_383_, 5, v_logMessage_371_);
lean_closure_set(v___f_383_, 6, v_toBind_372_);
lean_closure_set(v___f_383_, 7, v___f_373_);
lean_closure_set(v___f_383_, 8, v_getFileName_374_);
lean_closure_set(v___f_383_, 9, v_inst_375_);
lean_closure_set(v___f_383_, 10, v___f_376_);
lean_closure_set(v___f_383_, 11, v_env_377_);
lean_closure_set(v___f_383_, 12, v_val_378_);
lean_closure_set(v___f_383_, 13, v___y_368_);
lean_closure_set(v___f_383_, 14, v___x_379_);
v___x_384_ = lean_apply_4(v_toBind_372_, lean_box(0), lean_box(0), v_inst_380_, v___f_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_inst_385_, lean_object* v_source_386_, lean_object* v_text_387_, lean_object* v___y_388_, lean_object* v_inst_389_, lean_object* v_toApplicative_390_, lean_object* v_toBind_391_, lean_object* v___f_392_, lean_object* v_inst_393_, lean_object* v___f_394_, lean_object* v_val_395_, lean_object* v___x_396_, lean_object* v_inst_397_, lean_object* v_env_398_){
_start:
{
lean_object* v_getFileName_399_; lean_object* v_logMessage_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v_getFileName_399_ = lean_ctor_get(v_inst_385_, 2);
lean_inc_n(v_getFileName_399_, 2);
v_logMessage_400_ = lean_ctor_get(v_inst_385_, 4);
lean_inc(v_logMessage_400_);
lean_dec_ref(v_inst_385_);
lean_inc(v_toBind_391_);
v___f_401_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 16, 15);
lean_closure_set(v___f_401_, 0, v_source_386_);
lean_closure_set(v___f_401_, 1, v_text_387_);
lean_closure_set(v___f_401_, 2, v___y_388_);
lean_closure_set(v___f_401_, 3, v_inst_389_);
lean_closure_set(v___f_401_, 4, v_toApplicative_390_);
lean_closure_set(v___f_401_, 5, v_logMessage_400_);
lean_closure_set(v___f_401_, 6, v_toBind_391_);
lean_closure_set(v___f_401_, 7, v___f_392_);
lean_closure_set(v___f_401_, 8, v_getFileName_399_);
lean_closure_set(v___f_401_, 9, v_inst_393_);
lean_closure_set(v___f_401_, 10, v___f_394_);
lean_closure_set(v___f_401_, 11, v_env_398_);
lean_closure_set(v___f_401_, 12, v_val_395_);
lean_closure_set(v___f_401_, 13, v___x_396_);
lean_closure_set(v___f_401_, 14, v_inst_397_);
v___x_402_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v_getFileName_399_, v___f_401_);
return v___x_402_;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__11___closed__0));
v___x_405_ = l_Lean_stringToMessageData(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* v_docComment_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_toApplicative_410_, lean_object* v_toBind_411_, lean_object* v___f_412_, lean_object* v_inst_413_, lean_object* v___f_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_text_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = l_Lean_Syntax_getArg(v_docComment_406_, v___x_418_);
v___x_420_ = 1;
v___x_421_ = l_Lean_Syntax_getPos_x3f(v___x_419_, v___x_420_);
if (lean_obj_tag(v___x_421_) == 1)
{
lean_object* v_val_422_; lean_object* v___x_423_; 
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = l_Lean_Syntax_getTailPos_x3f(v___x_419_, v___x_420_);
lean_dec(v___x_419_);
if (lean_obj_tag(v___x_423_) == 1)
{
lean_object* v_val_424_; lean_object* v_source_425_; lean_object* v___y_427_; lean_object* v___x_431_; lean_object* v_endPos_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
lean_dec_ref(v_inst_416_);
lean_dec(v_docComment_406_);
v_val_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v___x_423_, 1);
v_source_425_ = lean_ctor_get(v_text_417_, 0);
lean_inc_ref(v_source_425_);
v___x_431_ = lean_string_utf8_prev(v_source_425_, v_val_424_);
lean_dec(v_val_424_);
v_endPos_432_ = lean_string_utf8_prev(v_source_425_, v___x_431_);
lean_dec(v___x_431_);
v___x_433_ = lean_string_utf8_byte_size(v_source_425_);
v___x_434_ = lean_nat_dec_le(v_endPos_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v_endPos_432_);
v___y_427_ = v___x_433_;
goto v___jp_426_;
}
else
{
v___y_427_ = v_endPos_432_;
goto v___jp_426_;
}
v___jp_426_:
{
lean_object* v_getEnv_428_; lean_object* v___f_429_; lean_object* v___x_430_; 
v_getEnv_428_ = lean_ctor_get(v_inst_407_, 0);
lean_inc(v_getEnv_428_);
lean_dec_ref(v_inst_407_);
lean_inc(v_toBind_411_);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 14, 13);
lean_closure_set(v___f_429_, 0, v_inst_408_);
lean_closure_set(v___f_429_, 1, v_source_425_);
lean_closure_set(v___f_429_, 2, v_text_417_);
lean_closure_set(v___f_429_, 3, v___y_427_);
lean_closure_set(v___f_429_, 4, v_inst_409_);
lean_closure_set(v___f_429_, 5, v_toApplicative_410_);
lean_closure_set(v___f_429_, 6, v_toBind_411_);
lean_closure_set(v___f_429_, 7, v___f_412_);
lean_closure_set(v___f_429_, 8, v_inst_413_);
lean_closure_set(v___f_429_, 9, v___f_414_);
lean_closure_set(v___f_429_, 10, v_val_422_);
lean_closure_set(v___f_429_, 11, v___x_418_);
lean_closure_set(v___f_429_, 12, v_inst_415_);
v___x_430_ = lean_apply_4(v_toBind_411_, lean_box(0), lean_box(0), v_getEnv_428_, v___f_429_);
return v___x_430_;
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v___x_423_);
lean_dec(v_val_422_);
lean_dec_ref(v_text_417_);
lean_dec(v_inst_415_);
lean_dec(v___f_414_);
lean_dec(v___f_412_);
lean_dec(v_toBind_411_);
lean_dec_ref(v_toApplicative_410_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
v___x_435_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_436_ = l_Lean_throwErrorAt___redArg(v_inst_413_, v_inst_416_, v_docComment_406_, v___x_435_);
return v___x_436_;
}
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec(v___x_421_);
lean_dec(v___x_419_);
lean_dec_ref(v_text_417_);
lean_dec(v_inst_415_);
lean_dec(v___f_414_);
lean_dec(v___f_412_);
lean_dec(v_toBind_411_);
lean_dec_ref(v_toApplicative_410_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
lean_dec_ref(v_inst_407_);
v___x_437_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_438_ = l_Lean_throwErrorAt___redArg(v_inst_413_, v_inst_416_, v_docComment_406_, v___x_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_docComment_456_){
_start:
{
lean_object* v_toApplicative_457_; lean_object* v_toBind_458_; lean_object* v___f_459_; lean_object* v___f_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_toApplicative_457_ = lean_ctor_get(v_inst_449_, 0);
lean_inc_ref_n(v_toApplicative_457_, 4);
v_toBind_458_ = lean_ctor_get(v_inst_449_, 1);
lean_inc_n(v_toBind_458_, 2);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_459_, 0, v_toApplicative_457_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_460_, 0, v_toApplicative_457_);
lean_inc_n(v_docComment_456_, 2);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 12, 11);
lean_closure_set(v___f_461_, 0, v_docComment_456_);
lean_closure_set(v___f_461_, 1, v_inst_452_);
lean_closure_set(v___f_461_, 2, v_inst_454_);
lean_closure_set(v___f_461_, 3, v_inst_455_);
lean_closure_set(v___f_461_, 4, v_toApplicative_457_);
lean_closure_set(v___f_461_, 5, v_toBind_458_);
lean_closure_set(v___f_461_, 6, v___f_460_);
lean_closure_set(v___f_461_, 7, v_inst_449_);
lean_closure_set(v___f_461_, 8, v___f_459_);
lean_closure_set(v___f_461_, 9, v_inst_453_);
lean_closure_set(v___f_461_, 10, v_inst_451_);
v___x_462_ = l_Lean_Syntax_getKind(v_docComment_456_);
v___x_463_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_464_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_465_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_466_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_467_ = lean_name_eq(v___x_462_, v___x_466_);
lean_dec(v___x_462_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec_ref(v_toApplicative_457_);
lean_dec(v_docComment_456_);
v___x_468_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_Lean_Syntax_getArg(v_docComment_456_, v___x_469_);
lean_dec(v_docComment_456_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_kind_471_; 
v_kind_471_ = lean_ctor_get(v___x_470_, 1);
lean_inc(v_kind_471_);
if (lean_obj_tag(v_kind_471_) == 1)
{
lean_object* v_pre_472_; 
v_pre_472_ = lean_ctor_get(v_kind_471_, 0);
lean_inc(v_pre_472_);
if (lean_obj_tag(v_pre_472_) == 1)
{
lean_object* v_pre_473_; 
v_pre_473_ = lean_ctor_get(v_pre_472_, 0);
lean_inc(v_pre_473_);
if (lean_obj_tag(v_pre_473_) == 1)
{
lean_object* v_pre_474_; 
v_pre_474_ = lean_ctor_get(v_pre_473_, 0);
lean_inc(v_pre_474_);
if (lean_obj_tag(v_pre_474_) == 1)
{
lean_object* v_pre_475_; 
v_pre_475_ = lean_ctor_get(v_pre_474_, 0);
lean_inc(v_pre_475_);
if (lean_obj_tag(v_pre_475_) == 0)
{
lean_object* v_info_476_; lean_object* v_args_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_509_; 
v_info_476_ = lean_ctor_get(v___x_470_, 0);
v_args_477_ = lean_ctor_get(v___x_470_, 2);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_509_ == 0)
{
lean_object* v_unused_510_; 
v_unused_510_ = lean_ctor_get(v___x_470_, 1);
lean_dec(v_unused_510_);
v___x_479_ = v___x_470_;
v_isShared_480_ = v_isSharedCheck_509_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_args_477_);
lean_inc(v_info_476_);
lean_dec(v___x_470_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_509_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_str_481_; lean_object* v_str_482_; lean_object* v_str_483_; lean_object* v_str_484_; uint8_t v___x_485_; 
v_str_481_ = lean_ctor_get(v_kind_471_, 1);
lean_inc_ref(v_str_481_);
lean_dec_ref_known(v_kind_471_, 2);
v_str_482_ = lean_ctor_get(v_pre_472_, 1);
lean_inc_ref(v_str_482_);
lean_dec_ref_known(v_pre_472_, 2);
v_str_483_ = lean_ctor_get(v_pre_473_, 1);
lean_inc_ref(v_str_483_);
lean_dec_ref_known(v_pre_473_, 2);
v_str_484_ = lean_ctor_get(v_pre_474_, 1);
lean_inc_ref(v_str_484_);
lean_dec_ref_known(v_pre_474_, 2);
v___x_485_ = lean_string_dec_eq(v_str_484_, v___x_463_);
lean_dec_ref(v_str_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_str_483_);
lean_dec_ref(v_str_482_);
lean_dec_ref(v_str_481_);
lean_del_object(v___x_479_);
lean_dec_ref(v_args_477_);
lean_dec(v_info_476_);
lean_dec_ref(v_toApplicative_457_);
v___x_486_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_486_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = lean_string_dec_eq(v_str_483_, v___x_464_);
lean_dec_ref(v_str_483_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_str_482_);
lean_dec_ref(v_str_481_);
lean_del_object(v___x_479_);
lean_dec_ref(v_args_477_);
lean_dec(v_info_476_);
lean_dec_ref(v_toApplicative_457_);
v___x_488_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = lean_string_dec_eq(v_str_482_, v___x_465_);
lean_dec_ref(v_str_482_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v_str_481_);
lean_del_object(v___x_479_);
lean_dec_ref(v_args_477_);
lean_dec(v_info_476_);
lean_dec_ref(v_toApplicative_457_);
v___x_490_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_492_ = lean_string_dec_eq(v_str_481_, v___x_491_);
lean_dec_ref(v_str_481_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_args_477_);
lean_dec(v_info_476_);
lean_dec_ref(v_toApplicative_457_);
v___x_493_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_493_;
}
else
{
lean_dec_ref(v___f_461_);
lean_dec(v_toBind_458_);
lean_dec(v_inst_450_);
if (v___x_492_ == 0)
{
lean_object* v_toPure_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_del_object(v___x_479_);
lean_dec_ref(v_args_477_);
lean_dec(v_info_476_);
v_toPure_494_ = lean_ctor_get(v_toApplicative_457_, 1);
lean_inc(v_toPure_494_);
lean_dec_ref(v_toApplicative_457_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_2(v_toPure_494_, lean_box(0), v___x_495_);
return v___x_496_;
}
else
{
lean_object* v_toPure_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v_toPure_497_ = lean_ctor_get(v_toApplicative_457_, 1);
lean_inc(v_toPure_497_);
lean_dec_ref(v_toApplicative_457_);
v___x_498_ = l_Lean_Name_str___override(v_pre_475_, v___x_463_);
v___x_499_ = l_Lean_Name_str___override(v___x_498_, v___x_464_);
v___x_500_ = l_Lean_Name_str___override(v___x_499_, v___x_465_);
v___x_501_ = l_Lean_Name_str___override(v___x_500_, v___x_491_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_501_);
v___x_503_ = v___x_479_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_info_476_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_args_477_);
v___x_503_ = v_reuseFailAlloc_508_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = l_Lean_Syntax_getArg(v___x_503_, v___x_504_);
lean_dec_ref(v___x_503_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
v___x_507_ = lean_apply_2(v_toPure_497_, lean_box(0), v___x_506_);
return v___x_507_;
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
lean_object* v___x_511_; 
lean_dec(v_pre_475_);
lean_dec_ref_known(v_pre_474_, 2);
lean_dec_ref_known(v_pre_473_, 2);
lean_dec_ref_known(v_pre_472_, 2);
lean_dec_ref_known(v_kind_471_, 2);
lean_dec_ref_known(v___x_470_, 3);
lean_dec_ref(v_toApplicative_457_);
v___x_511_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref_known(v_pre_473_, 2);
lean_dec(v_pre_474_);
lean_dec_ref_known(v_pre_472_, 2);
lean_dec_ref_known(v_kind_471_, 2);
lean_dec_ref_known(v___x_470_, 3);
lean_dec_ref(v_toApplicative_457_);
v___x_512_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; 
lean_dec(v_pre_473_);
lean_dec_ref_known(v_pre_472_, 2);
lean_dec_ref_known(v_kind_471_, 2);
lean_dec_ref_known(v___x_470_, 3);
lean_dec_ref(v_toApplicative_457_);
v___x_513_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref_known(v_kind_471_, 2);
lean_dec(v_pre_472_);
lean_dec_ref_known(v___x_470_, 3);
lean_dec_ref(v_toApplicative_457_);
v___x_514_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_514_;
}
}
else
{
lean_object* v___x_515_; 
lean_dec(v_kind_471_);
lean_dec_ref_known(v___x_470_, 3);
lean_dec_ref(v_toApplicative_457_);
v___x_515_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; 
lean_dec(v___x_470_);
lean_dec_ref(v_toApplicative_457_);
v___x_516_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v_inst_450_, v___f_461_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_docComment_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_parseVersoDocString___redArg(v_inst_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_docComment_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v___y_527_, lean_object* v_text_528_, lean_object* v_source_529_, lean_object* v_logMessage_530_, lean_object* v_____do__lift_531_){
_start:
{
lean_object* v_pos_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; uint8_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint32_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_pos_532_ = lean_ctor_get(v___y_527_, 2);
v___x_533_ = l_Lean_FileMap_toPosition(v_text_528_, v_pos_532_);
v___x_534_ = lean_box(0);
v___x_535_ = 0;
v___x_536_ = 2;
v___x_537_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
v___x_538_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__1));
v___x_539_ = lean_string_utf8_get(v_source_529_, v_pos_532_);
v___x_540_ = lean_string_push(v___x_537_, v___x_539_);
v___x_541_ = lean_string_append(v___x_538_, v___x_540_);
lean_dec_ref(v___x_540_);
v___x_542_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__2));
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
v___x_545_ = l_Lean_MessageData_ofFormat(v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_546_, 0, v_____do__lift_531_);
lean_ctor_set(v___x_546_, 1, v___x_533_);
lean_ctor_set(v___x_546_, 2, v___x_534_);
lean_ctor_set(v___x_546_, 3, v___x_537_);
lean_ctor_set(v___x_546_, 4, v___x_545_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*5, v___x_535_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*5 + 1, v___x_536_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*5 + 2, v___x_535_);
v___x_547_ = lean_apply_1(v_logMessage_530_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v___y_548_, lean_object* v_text_549_, lean_object* v_source_550_, lean_object* v_logMessage_551_, lean_object* v_____do__lift_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v___y_548_, v_text_549_, v_source_550_, v_logMessage_551_, v_____do__lift_552_);
lean_dec_ref(v_source_550_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v_toPure_554_, lean_object* v_toBind_555_, lean_object* v_getFileName_556_, lean_object* v___f_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v___y_560_, lean_object* v_ictx_561_, lean_object* v_____s_562_){
_start:
{
uint8_t v___y_564_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_array_get_size(v___x_558_);
v___x_569_ = lean_nat_dec_eq(v___x_568_, v___x_559_);
if (v___x_569_ == 0)
{
v___y_564_ = v___x_569_;
goto v___jp_563_;
}
else
{
lean_object* v_pos_570_; uint8_t v___x_571_; uint8_t v___x_572_; 
v_pos_570_ = lean_ctor_get(v___y_560_, 2);
v___x_571_ = l_Lean_Parser_InputContext_atEnd(v_ictx_561_, v_pos_570_);
v___x_572_ = lean_bool_not(v___x_571_);
v___y_564_ = v___x_572_;
goto v___jp_563_;
}
v___jp_563_:
{
if (v___y_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___f_557_);
lean_dec(v_getFileName_556_);
lean_dec(v_toBind_555_);
v___x_565_ = lean_box(0);
v___x_566_ = lean_apply_2(v_toPure_554_, lean_box(0), v___x_565_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; 
lean_dec(v_toPure_554_);
v___x_567_ = lean_apply_4(v_toBind_555_, lean_box(0), lean_box(0), v_getFileName_556_, v___f_557_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object* v_toPure_573_, lean_object* v_toBind_574_, lean_object* v_getFileName_575_, lean_object* v___f_576_, lean_object* v___x_577_, lean_object* v___x_578_, lean_object* v___y_579_, lean_object* v_ictx_580_, lean_object* v_____s_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_reportVersoParseFailure___redArg___lam__1(v_toPure_573_, v_toBind_574_, v_getFileName_575_, v___f_576_, v___x_577_, v___x_578_, v___y_579_, v_ictx_580_, v_____s_581_);
lean_dec_ref(v_ictx_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___x_578_);
lean_dec_ref(v___x_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v___x_583_, lean_object* v_toPure_584_, lean_object* v_____r_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_583_);
v___x_587_ = lean_apply_2(v_toPure_584_, lean_box(0), v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_text_588_, lean_object* v_source_589_, lean_object* v_logMessage_590_, lean_object* v_toPure_591_, lean_object* v_toBind_592_, lean_object* v_getFileName_593_, lean_object* v___x_594_, lean_object* v_ictx_595_, lean_object* v_inst_596_, lean_object* v_env_597_, lean_object* v_____do__lift_598_, lean_object* v_____do__lift_599_, lean_object* v_val_600_, lean_object* v___y_601_, lean_object* v_____do__lift_602_){
_start:
{
lean_object* v___y_604_; lean_object* v_pmctx_615_; lean_object* v_blockCtxt_616_; lean_object* v___x_617_; lean_object* v_s_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_s_621_; uint8_t v___y_623_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
lean_inc_ref(v_env_597_);
v_pmctx_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_615_, 0, v_env_597_);
lean_ctor_set(v_pmctx_615_, 1, v_____do__lift_598_);
lean_ctor_set(v_pmctx_615_, 2, v_____do__lift_599_);
lean_ctor_set(v_pmctx_615_, 3, v_____do__lift_602_);
lean_inc(v_val_600_);
lean_inc_ref(v_text_588_);
v_blockCtxt_616_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_588_, v_val_600_, v___y_601_);
v___x_617_ = l_Lean_Parser_mkParserState(v_source_589_);
lean_inc_ref(v___x_617_);
v_s_618_ = l_Lean_Parser_ParserState_setPos(v___x_617_, v_val_600_);
v___x_619_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_619_, 0, v_blockCtxt_616_);
v___x_620_ = l_Lean_Parser_getTokenTable(v_env_597_);
lean_inc_ref(v___x_620_);
lean_inc_ref(v_pmctx_615_);
lean_inc_ref(v_ictx_595_);
v_s_621_ = l_Lean_Parser_ParserFn_run(v___x_619_, v_ictx_595_, v_pmctx_615_, v___x_620_, v_s_618_);
lean_inc_ref(v_s_621_);
v___x_633_ = l_Lean_Parser_ParserState_allErrors(v_s_621_);
v___x_634_ = lean_array_get_size(v___x_633_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_nat_dec_eq(v___x_634_, v___x_594_);
if (v___x_635_ == 0)
{
v___y_623_ = v___x_635_;
goto v___jp_622_;
}
else
{
lean_object* v_pos_636_; uint8_t v___x_637_; uint8_t v___x_638_; 
v_pos_636_ = lean_ctor_get(v_s_621_, 2);
lean_inc(v_pos_636_);
v___x_637_ = l_Lean_Parser_InputContext_atEnd(v_ictx_595_, v_pos_636_);
lean_dec(v_pos_636_);
v___x_638_ = lean_bool_not(v___x_637_);
v___y_623_ = v___x_638_;
goto v___jp_622_;
}
v___jp_603_:
{
lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___f_610_; size_t v_sz_611_; size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
lean_inc(v_logMessage_590_);
lean_inc_ref(v_text_588_);
lean_inc_ref_n(v___y_604_, 2);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_605_, 0, v___y_604_);
lean_closure_set(v___f_605_, 1, v_text_588_);
lean_closure_set(v___f_605_, 2, v_source_589_);
lean_closure_set(v___f_605_, 3, v_logMessage_590_);
v___x_606_ = l_Lean_Parser_ParserState_allErrors(v___y_604_);
lean_inc_ref(v___x_606_);
lean_inc(v_getFileName_593_);
lean_inc_n(v_toBind_592_, 2);
lean_inc(v_toPure_591_);
v___f_607_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_607_, 0, v_toPure_591_);
lean_closure_set(v___f_607_, 1, v_toBind_592_);
lean_closure_set(v___f_607_, 2, v_getFileName_593_);
lean_closure_set(v___f_607_, 3, v___f_605_);
lean_closure_set(v___f_607_, 4, v___x_606_);
lean_closure_set(v___f_607_, 5, v___x_594_);
lean_closure_set(v___f_607_, 6, v___y_604_);
lean_closure_set(v___f_607_, 7, v_ictx_595_);
v___x_608_ = lean_box(0);
v___f_609_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2), 3, 2);
lean_closure_set(v___f_609_, 0, v___x_608_);
lean_closure_set(v___f_609_, 1, v_toPure_591_);
v___f_610_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5), 8, 5);
lean_closure_set(v___f_610_, 0, v_text_588_);
lean_closure_set(v___f_610_, 1, v_logMessage_590_);
lean_closure_set(v___f_610_, 2, v_toBind_592_);
lean_closure_set(v___f_610_, 3, v___f_609_);
lean_closure_set(v___f_610_, 4, v_getFileName_593_);
v_sz_611_ = lean_array_size(v___x_606_);
v___x_612_ = ((size_t)0ULL);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_596_, v___x_606_, v___f_610_, v_sz_611_, v___x_612_, v___x_608_);
v___x_614_ = lean_apply_4(v_toBind_592_, lean_box(0), lean_box(0), v___x_613_, v___f_607_);
return v___x_614_;
}
v___jp_622_:
{
if (v___y_623_ == 0)
{
lean_dec_ref(v___x_620_);
lean_dec_ref(v___x_617_);
lean_dec_ref_known(v_pmctx_615_, 4);
v___y_604_ = v_s_621_;
goto v___jp_603_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_pos_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_box(0);
v___x_626_ = lean_unsigned_to_nat(1u);
lean_inc_n(v___x_594_, 3);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_594_);
v___x_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_628_, 0, v___x_594_);
lean_ctor_set(v___x_628_, 1, v___x_624_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
lean_ctor_set(v___x_628_, 3, v___x_627_);
lean_ctor_set(v___x_628_, 4, v___x_594_);
v_pos_629_ = lean_ctor_get(v_s_621_, 2);
lean_inc(v_pos_629_);
lean_dec_ref(v_s_621_);
v___x_630_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_630_, 0, v___x_628_);
v___x_631_ = l_Lean_Parser_ParserState_setPos(v___x_617_, v_pos_629_);
lean_inc_ref(v_ictx_595_);
v___x_632_ = l_Lean_Parser_ParserFn_run(v___x_630_, v_ictx_595_, v_pmctx_615_, v___x_620_, v___x_631_);
v___y_604_ = v___x_632_;
goto v___jp_603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_text_639_, lean_object* v_source_640_, lean_object* v_logMessage_641_, lean_object* v_toPure_642_, lean_object* v_toBind_643_, lean_object* v_getFileName_644_, lean_object* v___x_645_, lean_object* v_ictx_646_, lean_object* v_inst_647_, lean_object* v_env_648_, lean_object* v_____do__lift_649_, lean_object* v_val_650_, lean_object* v___y_651_, lean_object* v_getOpenDecls_652_, lean_object* v_____do__lift_653_){
_start:
{
lean_object* v___f_654_; lean_object* v___x_655_; 
lean_inc(v_toBind_643_);
v___f_654_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(v___f_654_, 0, v_text_639_);
lean_closure_set(v___f_654_, 1, v_source_640_);
lean_closure_set(v___f_654_, 2, v_logMessage_641_);
lean_closure_set(v___f_654_, 3, v_toPure_642_);
lean_closure_set(v___f_654_, 4, v_toBind_643_);
lean_closure_set(v___f_654_, 5, v_getFileName_644_);
lean_closure_set(v___f_654_, 6, v___x_645_);
lean_closure_set(v___f_654_, 7, v_ictx_646_);
lean_closure_set(v___f_654_, 8, v_inst_647_);
lean_closure_set(v___f_654_, 9, v_env_648_);
lean_closure_set(v___f_654_, 10, v_____do__lift_649_);
lean_closure_set(v___f_654_, 11, v_____do__lift_653_);
lean_closure_set(v___f_654_, 12, v_val_650_);
lean_closure_set(v___f_654_, 13, v___y_651_);
v___x_655_ = lean_apply_4(v_toBind_643_, lean_box(0), lean_box(0), v_getOpenDecls_652_, v___f_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_inst_656_, lean_object* v_text_657_, lean_object* v_source_658_, lean_object* v_logMessage_659_, lean_object* v_toPure_660_, lean_object* v_toBind_661_, lean_object* v_getFileName_662_, lean_object* v___x_663_, lean_object* v_ictx_664_, lean_object* v_inst_665_, lean_object* v_env_666_, lean_object* v_val_667_, lean_object* v___y_668_, lean_object* v_____do__lift_669_){
_start:
{
lean_object* v_getCurrNamespace_670_; lean_object* v_getOpenDecls_671_; lean_object* v___f_672_; lean_object* v___x_673_; 
v_getCurrNamespace_670_ = lean_ctor_get(v_inst_656_, 0);
lean_inc(v_getCurrNamespace_670_);
v_getOpenDecls_671_ = lean_ctor_get(v_inst_656_, 1);
lean_inc(v_getOpenDecls_671_);
lean_dec_ref(v_inst_656_);
lean_inc(v_toBind_661_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3), 15, 14);
lean_closure_set(v___f_672_, 0, v_text_657_);
lean_closure_set(v___f_672_, 1, v_source_658_);
lean_closure_set(v___f_672_, 2, v_logMessage_659_);
lean_closure_set(v___f_672_, 3, v_toPure_660_);
lean_closure_set(v___f_672_, 4, v_toBind_661_);
lean_closure_set(v___f_672_, 5, v_getFileName_662_);
lean_closure_set(v___f_672_, 6, v___x_663_);
lean_closure_set(v___f_672_, 7, v_ictx_664_);
lean_closure_set(v___f_672_, 8, v_inst_665_);
lean_closure_set(v___f_672_, 9, v_env_666_);
lean_closure_set(v___f_672_, 10, v_____do__lift_669_);
lean_closure_set(v___f_672_, 11, v_val_667_);
lean_closure_set(v___f_672_, 12, v___y_668_);
lean_closure_set(v___f_672_, 13, v_getOpenDecls_671_);
v___x_673_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v_getCurrNamespace_670_, v___f_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_source_674_, lean_object* v_text_675_, lean_object* v___y_676_, lean_object* v_inst_677_, lean_object* v_logMessage_678_, lean_object* v_toPure_679_, lean_object* v_toBind_680_, lean_object* v_getFileName_681_, lean_object* v___x_682_, lean_object* v_inst_683_, lean_object* v_env_684_, lean_object* v_val_685_, lean_object* v_inst_686_, lean_object* v_____do__lift_687_){
_start:
{
lean_object* v_ictx_688_; lean_object* v___f_689_; lean_object* v___x_690_; 
lean_inc(v___y_676_);
lean_inc_ref(v_text_675_);
lean_inc_ref(v_source_674_);
v_ictx_688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_688_, 0, v_source_674_);
lean_ctor_set(v_ictx_688_, 1, v_____do__lift_687_);
lean_ctor_set(v_ictx_688_, 2, v_text_675_);
lean_ctor_set(v_ictx_688_, 3, v___y_676_);
lean_inc(v_toBind_680_);
v___f_689_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4), 14, 13);
lean_closure_set(v___f_689_, 0, v_inst_677_);
lean_closure_set(v___f_689_, 1, v_text_675_);
lean_closure_set(v___f_689_, 2, v_source_674_);
lean_closure_set(v___f_689_, 3, v_logMessage_678_);
lean_closure_set(v___f_689_, 4, v_toPure_679_);
lean_closure_set(v___f_689_, 5, v_toBind_680_);
lean_closure_set(v___f_689_, 6, v_getFileName_681_);
lean_closure_set(v___f_689_, 7, v___x_682_);
lean_closure_set(v___f_689_, 8, v_ictx_688_);
lean_closure_set(v___f_689_, 9, v_inst_683_);
lean_closure_set(v___f_689_, 10, v_env_684_);
lean_closure_set(v___f_689_, 11, v_val_685_);
lean_closure_set(v___f_689_, 12, v___y_676_);
v___x_690_ = lean_apply_4(v_toBind_680_, lean_box(0), lean_box(0), v_inst_686_, v___f_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_inst_691_, lean_object* v_source_692_, lean_object* v_text_693_, lean_object* v___y_694_, lean_object* v_inst_695_, lean_object* v_toPure_696_, lean_object* v_toBind_697_, lean_object* v___x_698_, lean_object* v_inst_699_, lean_object* v_val_700_, lean_object* v_inst_701_, lean_object* v_env_702_){
_start:
{
lean_object* v_getFileName_703_; lean_object* v_logMessage_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v_getFileName_703_ = lean_ctor_get(v_inst_691_, 2);
lean_inc_n(v_getFileName_703_, 2);
v_logMessage_704_ = lean_ctor_get(v_inst_691_, 4);
lean_inc(v_logMessage_704_);
lean_dec_ref(v_inst_691_);
lean_inc(v_toBind_697_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 14, 13);
lean_closure_set(v___f_705_, 0, v_source_692_);
lean_closure_set(v___f_705_, 1, v_text_693_);
lean_closure_set(v___f_705_, 2, v___y_694_);
lean_closure_set(v___f_705_, 3, v_inst_695_);
lean_closure_set(v___f_705_, 4, v_logMessage_704_);
lean_closure_set(v___f_705_, 5, v_toPure_696_);
lean_closure_set(v___f_705_, 6, v_toBind_697_);
lean_closure_set(v___f_705_, 7, v_getFileName_703_);
lean_closure_set(v___f_705_, 8, v___x_698_);
lean_closure_set(v___f_705_, 9, v_inst_699_);
lean_closure_set(v___f_705_, 10, v_env_702_);
lean_closure_set(v___f_705_, 11, v_val_700_);
lean_closure_set(v___f_705_, 12, v_inst_701_);
v___x_706_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v_getFileName_703_, v___f_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_toPure_710_, lean_object* v_toBind_711_, lean_object* v___x_712_, lean_object* v_inst_713_, lean_object* v_val_714_, lean_object* v_inst_715_, lean_object* v_val_716_, lean_object* v_text_717_){
_start:
{
lean_object* v_source_718_; lean_object* v___y_720_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_source_718_ = lean_ctor_get(v_text_717_, 0);
lean_inc_ref(v_source_718_);
v___x_724_ = lean_string_utf8_byte_size(v_source_718_);
v___x_725_ = lean_nat_dec_le(v_val_716_, v___x_724_);
if (v___x_725_ == 0)
{
lean_dec(v_val_716_);
v___y_720_ = v___x_724_;
goto v___jp_719_;
}
else
{
v___y_720_ = v_val_716_;
goto v___jp_719_;
}
v___jp_719_:
{
lean_object* v_getEnv_721_; lean_object* v___f_722_; lean_object* v___x_723_; 
v_getEnv_721_ = lean_ctor_get(v_inst_707_, 0);
lean_inc(v_getEnv_721_);
lean_dec_ref(v_inst_707_);
lean_inc(v_toBind_711_);
v___f_722_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 12, 11);
lean_closure_set(v___f_722_, 0, v_inst_708_);
lean_closure_set(v___f_722_, 1, v_source_718_);
lean_closure_set(v___f_722_, 2, v_text_717_);
lean_closure_set(v___f_722_, 3, v___y_720_);
lean_closure_set(v___f_722_, 4, v_inst_709_);
lean_closure_set(v___f_722_, 5, v_toPure_710_);
lean_closure_set(v___f_722_, 6, v_toBind_711_);
lean_closure_set(v___f_722_, 7, v___x_712_);
lean_closure_set(v___f_722_, 8, v_inst_713_);
lean_closure_set(v___f_722_, 9, v_val_714_);
lean_closure_set(v___f_722_, 10, v_inst_715_);
v___x_723_ = lean_apply_4(v_toBind_711_, lean_box(0), lean_box(0), v_getEnv_721_, v___f_722_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_parseFailure_732_){
_start:
{
lean_object* v_toApplicative_733_; lean_object* v_toBind_734_; lean_object* v_toPure_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; 
v_toApplicative_733_ = lean_ctor_get(v_inst_726_, 0);
v_toBind_734_ = lean_ctor_get(v_inst_726_, 1);
lean_inc(v_toBind_734_);
v_toPure_735_ = lean_ctor_get(v_toApplicative_733_, 1);
lean_inc(v_toPure_735_);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = l_Lean_Syntax_getArg(v_parseFailure_732_, v___x_736_);
v___x_738_ = 1;
v___x_739_ = l_Lean_Syntax_getPos_x3f(v___x_737_, v___x_738_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_val_740_; lean_object* v___x_741_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_Syntax_getTailPos_x3f(v___x_737_, v___x_738_);
lean_dec(v___x_737_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___f_743_; lean_object* v___x_744_; 
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_741_, 1);
lean_inc(v_toBind_734_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 11, 10);
lean_closure_set(v___f_743_, 0, v_inst_728_);
lean_closure_set(v___f_743_, 1, v_inst_730_);
lean_closure_set(v___f_743_, 2, v_inst_731_);
lean_closure_set(v___f_743_, 3, v_toPure_735_);
lean_closure_set(v___f_743_, 4, v_toBind_734_);
lean_closure_set(v___f_743_, 5, v___x_736_);
lean_closure_set(v___f_743_, 6, v_inst_726_);
lean_closure_set(v___f_743_, 7, v_val_740_);
lean_closure_set(v___f_743_, 8, v_inst_729_);
lean_closure_set(v___f_743_, 9, v_val_742_);
v___x_744_ = lean_apply_4(v_toBind_734_, lean_box(0), lean_box(0), v_inst_727_, v___f_743_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec(v___x_741_);
lean_dec(v_val_740_);
lean_dec(v_toBind_734_);
lean_dec_ref(v_inst_731_);
lean_dec_ref(v_inst_730_);
lean_dec(v_inst_729_);
lean_dec_ref(v_inst_728_);
lean_dec(v_inst_727_);
lean_dec_ref(v_inst_726_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_apply_2(v_toPure_735_, lean_box(0), v___x_745_);
return v___x_746_;
}
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v___x_739_);
lean_dec(v___x_737_);
lean_dec(v_toBind_734_);
lean_dec_ref(v_inst_731_);
lean_dec_ref(v_inst_730_);
lean_dec(v_inst_729_);
lean_dec_ref(v_inst_728_);
lean_dec(v_inst_727_);
lean_dec_ref(v_inst_726_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_apply_2(v_toPure_735_, lean_box(0), v___x_747_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_parseFailure_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_reportVersoParseFailure___redArg(v_inst_749_, v_inst_750_, v_inst_751_, v_inst_752_, v_inst_753_, v_inst_754_, v_parseFailure_755_);
lean_dec(v_parseFailure_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_inst_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_parseFailure_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_reportVersoParseFailure___redArg(v_inst_758_, v_inst_759_, v_inst_761_, v_inst_762_, v_inst_763_, v_inst_764_, v_parseFailure_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_parseFailure_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_reportVersoParseFailure(v_m_767_, v_inst_768_, v_inst_769_, v_inst_770_, v_inst_771_, v_inst_772_, v_inst_773_, v_inst_774_, v_parseFailure_775_);
lean_dec(v_parseFailure_775_);
lean_dec_ref(v_inst_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_777_, lean_object* v_declName_778_, lean_object* v_binders_779_, lean_object* v___x_780_, uint8_t v___x_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_777_) == 0)
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Doc_DocM_exec___redArg(v_declName_778_, v_binders_779_, v___x_780_, v___x_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; lean_object* v_fileName_791_; lean_object* v_options_792_; lean_object* v_currRecDepth_793_; lean_object* v_maxRecDepth_794_; lean_object* v_ref_795_; lean_object* v_currNamespace_796_; lean_object* v_openDecls_797_; lean_object* v_initHeartbeats_798_; lean_object* v_maxHeartbeats_799_; lean_object* v_quotContext_800_; lean_object* v_currMacroScope_801_; uint8_t v_diag_802_; lean_object* v_cancelTk_x3f_803_; uint8_t v_suppressElabErrors_804_; lean_object* v_inheritedTraceOptions_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_790_ = lean_ctor_get(v_fileMap_x3f_777_, 0);
v_fileName_791_ = lean_ctor_get(v___y_786_, 0);
v_options_792_ = lean_ctor_get(v___y_786_, 2);
v_currRecDepth_793_ = lean_ctor_get(v___y_786_, 3);
v_maxRecDepth_794_ = lean_ctor_get(v___y_786_, 4);
v_ref_795_ = lean_ctor_get(v___y_786_, 5);
v_currNamespace_796_ = lean_ctor_get(v___y_786_, 6);
v_openDecls_797_ = lean_ctor_get(v___y_786_, 7);
v_initHeartbeats_798_ = lean_ctor_get(v___y_786_, 8);
v_maxHeartbeats_799_ = lean_ctor_get(v___y_786_, 9);
v_quotContext_800_ = lean_ctor_get(v___y_786_, 10);
v_currMacroScope_801_ = lean_ctor_get(v___y_786_, 11);
v_diag_802_ = lean_ctor_get_uint8(v___y_786_, sizeof(void*)*14);
v_cancelTk_x3f_803_ = lean_ctor_get(v___y_786_, 12);
v_suppressElabErrors_804_ = lean_ctor_get_uint8(v___y_786_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_805_ = lean_ctor_get(v___y_786_, 13);
lean_inc_ref(v_inheritedTraceOptions_805_);
lean_inc(v_cancelTk_x3f_803_);
lean_inc(v_currMacroScope_801_);
lean_inc(v_quotContext_800_);
lean_inc(v_maxHeartbeats_799_);
lean_inc(v_initHeartbeats_798_);
lean_inc(v_openDecls_797_);
lean_inc(v_currNamespace_796_);
lean_inc(v_ref_795_);
lean_inc(v_maxRecDepth_794_);
lean_inc(v_currRecDepth_793_);
lean_inc_ref(v_options_792_);
lean_inc(v_val_790_);
lean_inc_ref(v_fileName_791_);
v___x_806_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_806_, 0, v_fileName_791_);
lean_ctor_set(v___x_806_, 1, v_val_790_);
lean_ctor_set(v___x_806_, 2, v_options_792_);
lean_ctor_set(v___x_806_, 3, v_currRecDepth_793_);
lean_ctor_set(v___x_806_, 4, v_maxRecDepth_794_);
lean_ctor_set(v___x_806_, 5, v_ref_795_);
lean_ctor_set(v___x_806_, 6, v_currNamespace_796_);
lean_ctor_set(v___x_806_, 7, v_openDecls_797_);
lean_ctor_set(v___x_806_, 8, v_initHeartbeats_798_);
lean_ctor_set(v___x_806_, 9, v_maxHeartbeats_799_);
lean_ctor_set(v___x_806_, 10, v_quotContext_800_);
lean_ctor_set(v___x_806_, 11, v_currMacroScope_801_);
lean_ctor_set(v___x_806_, 12, v_cancelTk_x3f_803_);
lean_ctor_set(v___x_806_, 13, v_inheritedTraceOptions_805_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*14, v_diag_802_);
lean_ctor_set_uint8(v___x_806_, sizeof(void*)*14 + 1, v_suppressElabErrors_804_);
v___x_807_ = l_Lean_Doc_DocM_exec___redArg(v_declName_778_, v_binders_779_, v___x_780_, v___x_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___x_806_, v___y_787_);
lean_dec_ref_known(v___x_806_, 14);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_808_, lean_object* v_declName_809_, lean_object* v_binders_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___x_9417__boxed_820_; lean_object* v_res_821_; 
v___x_9417__boxed_820_ = lean_unbox(v___x_812_);
v_res_821_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_808_, v_declName_809_, v_binders_810_, v___x_811_, v___x_9417__boxed_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v_fileMap_x3f_808_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_822_, size_t v_i_823_, lean_object* v_bs_824_){
_start:
{
uint8_t v___x_825_; 
v___x_825_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_825_ == 0)
{
return v_bs_824_;
}
else
{
lean_object* v_v_826_; lean_object* v___x_827_; lean_object* v_bs_x27_828_; size_t v___x_829_; size_t v___x_830_; lean_object* v___x_831_; 
v_v_826_ = lean_array_uget(v_bs_824_, v_i_823_);
v___x_827_ = lean_unsigned_to_nat(0u);
v_bs_x27_828_ = lean_array_uset(v_bs_824_, v_i_823_, v___x_827_);
v___x_829_ = ((size_t)1ULL);
v___x_830_ = lean_usize_add(v_i_823_, v___x_829_);
v___x_831_ = lean_array_uset(v_bs_x27_828_, v_i_823_, v_v_826_);
v_i_823_ = v___x_830_;
v_bs_824_ = v___x_831_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_833_, lean_object* v_i_834_, lean_object* v_bs_835_){
_start:
{
size_t v_sz_boxed_836_; size_t v_i_boxed_837_; lean_object* v_res_838_; 
v_sz_boxed_836_ = lean_unbox_usize(v_sz_833_);
lean_dec(v_sz_833_);
v_i_boxed_837_ = lean_unbox_usize(v_i_834_);
lean_dec(v_i_834_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_836_, v_i_boxed_837_, v_bs_835_);
return v_res_838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_839_, lean_object* v_opt_840_){
_start:
{
lean_object* v_name_841_; lean_object* v_defValue_842_; lean_object* v_map_843_; lean_object* v___x_844_; 
v_name_841_ = lean_ctor_get(v_opt_840_, 0);
v_defValue_842_ = lean_ctor_get(v_opt_840_, 1);
v_map_843_ = lean_ctor_get(v_opts_839_, 0);
v___x_844_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_843_, v_name_841_);
if (lean_obj_tag(v___x_844_) == 0)
{
uint8_t v___x_845_; 
v___x_845_ = lean_unbox(v_defValue_842_);
return v___x_845_;
}
else
{
lean_object* v_val_846_; 
v_val_846_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v_val_846_) == 1)
{
uint8_t v_v_847_; 
v_v_847_ = lean_ctor_get_uint8(v_val_846_, 0);
lean_dec_ref_known(v_val_846_, 0);
return v_v_847_;
}
else
{
uint8_t v___x_848_; 
lean_dec(v_val_846_);
v___x_848_ = lean_unbox(v_defValue_842_);
return v___x_848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_849_, lean_object* v_opt_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_849_, v_opt_850_);
lean_dec_ref(v_opt_850_);
lean_dec_ref(v_opts_849_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v_env_860_; lean_object* v___x_861_; lean_object* v_mctx_862_; lean_object* v_lctx_863_; lean_object* v_options_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_859_ = lean_st_ref_get(v___y_857_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v___x_861_ = lean_st_ref_get(v___y_855_);
v_mctx_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_mctx_862_);
lean_dec(v___x_861_);
v_lctx_863_ = lean_ctor_get(v___y_854_, 2);
v_options_864_ = lean_ctor_get(v___y_856_, 2);
lean_inc_ref(v_options_864_);
lean_inc_ref(v_lctx_863_);
v___x_865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_865_, 0, v_env_860_);
lean_ctor_set(v___x_865_, 1, v_mctx_862_);
lean_ctor_set(v___x_865_, 2, v_lctx_863_);
lean_ctor_set(v___x_865_, 3, v_options_864_);
v___x_866_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v_msgData_853_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v___y_883_, uint8_t v_suppressElabErrors_884_, lean_object* v_x_885_){
_start:
{
if (lean_obj_tag(v_x_885_) == 1)
{
lean_object* v_pre_886_; 
v_pre_886_ = lean_ctor_get(v_x_885_, 0);
switch(lean_obj_tag(v_pre_886_))
{
case 1:
{
lean_object* v_pre_887_; 
v_pre_887_ = lean_ctor_get(v_pre_886_, 0);
switch(lean_obj_tag(v_pre_887_))
{
case 0:
{
lean_object* v_str_888_; lean_object* v_str_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v_str_888_ = lean_ctor_get(v_x_885_, 1);
v_str_889_ = lean_ctor_get(v_pre_886_, 1);
v___x_890_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_891_ = lean_string_dec_eq(v_str_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_893_ = lean_string_dec_eq(v_str_889_, v___x_892_);
if (v___x_893_ == 0)
{
return v___y_883_;
}
else
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_895_ = lean_string_dec_eq(v_str_888_, v___x_894_);
if (v___x_895_ == 0)
{
return v___y_883_;
}
else
{
return v_suppressElabErrors_884_;
}
}
}
else
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_897_ = lean_string_dec_eq(v_str_888_, v___x_896_);
if (v___x_897_ == 0)
{
return v___y_883_;
}
else
{
return v_suppressElabErrors_884_;
}
}
}
case 1:
{
lean_object* v_pre_898_; 
v_pre_898_ = lean_ctor_get(v_pre_887_, 0);
if (lean_obj_tag(v_pre_898_) == 0)
{
lean_object* v_str_899_; lean_object* v_str_900_; lean_object* v_str_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_str_899_ = lean_ctor_get(v_x_885_, 1);
v_str_900_ = lean_ctor_get(v_pre_886_, 1);
v_str_901_ = lean_ctor_get(v_pre_887_, 1);
v___x_902_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_903_ = lean_string_dec_eq(v_str_901_, v___x_902_);
if (v___x_903_ == 0)
{
return v___y_883_;
}
else
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_905_ = lean_string_dec_eq(v_str_900_, v___x_904_);
if (v___x_905_ == 0)
{
return v___y_883_;
}
else
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_907_ = lean_string_dec_eq(v_str_899_, v___x_906_);
if (v___x_907_ == 0)
{
return v___y_883_;
}
else
{
return v_suppressElabErrors_884_;
}
}
}
}
else
{
return v___y_883_;
}
}
default: 
{
return v___y_883_;
}
}
}
case 0:
{
lean_object* v_str_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_str_908_ = lean_ctor_get(v_x_885_, 1);
v___x_909_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_910_ = lean_string_dec_eq(v_str_908_, v___x_909_);
if (v___x_910_ == 0)
{
return v___y_883_;
}
else
{
return v_suppressElabErrors_884_;
}
}
default: 
{
return v___y_883_;
}
}
}
else
{
return v___y_883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v___y_911_, lean_object* v_suppressElabErrors_912_, lean_object* v_x_913_){
_start:
{
uint8_t v___y_9514__boxed_914_; uint8_t v_suppressElabErrors_boxed_915_; uint8_t v_res_916_; lean_object* v_r_917_; 
v___y_9514__boxed_914_ = lean_unbox(v___y_911_);
v_suppressElabErrors_boxed_915_ = lean_unbox(v_suppressElabErrors_912_);
v_res_916_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v___y_9514__boxed_914_, v_suppressElabErrors_boxed_915_, v_x_913_);
lean_dec(v_x_913_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_918_, lean_object* v_msgData_919_, uint8_t v_severity_920_, uint8_t v_isSilent_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___y_928_; lean_object* v___y_929_; uint8_t v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; uint8_t v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; uint8_t v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; uint8_t v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; uint8_t v___y_1004_; uint8_t v___y_1005_; uint8_t v___y_1006_; uint8_t v___x_1011_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; uint8_t v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1021_; uint8_t v___x_1036_; 
v___x_1011_ = 2;
v___x_1036_ = l_Lean_instBEqMessageSeverity_beq(v_severity_920_, v___x_1011_);
if (v___x_1036_ == 0)
{
v___y_1021_ = v___x_1036_;
goto v___jp_1020_;
}
else
{
uint8_t v___x_1037_; 
lean_inc_ref(v_msgData_919_);
v___x_1037_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_919_);
v___y_1021_ = v___x_1037_;
goto v___jp_1020_;
}
v___jp_927_:
{
lean_object* v___x_937_; lean_object* v_currNamespace_938_; lean_object* v_openDecls_939_; lean_object* v_env_940_; lean_object* v_nextMacroScope_941_; lean_object* v_ngen_942_; lean_object* v_auxDeclNGen_943_; lean_object* v_traceState_944_; lean_object* v_cache_945_; lean_object* v_messages_946_; lean_object* v_infoState_947_; lean_object* v_snapshotTasks_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_962_; 
v___x_937_ = lean_st_ref_take(v___y_936_);
v_currNamespace_938_ = lean_ctor_get(v___y_935_, 6);
v_openDecls_939_ = lean_ctor_get(v___y_935_, 7);
v_env_940_ = lean_ctor_get(v___x_937_, 0);
v_nextMacroScope_941_ = lean_ctor_get(v___x_937_, 1);
v_ngen_942_ = lean_ctor_get(v___x_937_, 2);
v_auxDeclNGen_943_ = lean_ctor_get(v___x_937_, 3);
v_traceState_944_ = lean_ctor_get(v___x_937_, 4);
v_cache_945_ = lean_ctor_get(v___x_937_, 5);
v_messages_946_ = lean_ctor_get(v___x_937_, 6);
v_infoState_947_ = lean_ctor_get(v___x_937_, 7);
v_snapshotTasks_948_ = lean_ctor_get(v___x_937_, 8);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_962_ == 0)
{
v___x_950_ = v___x_937_;
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snapshotTasks_948_);
lean_inc(v_infoState_947_);
lean_inc(v_messages_946_);
lean_inc(v_cache_945_);
lean_inc(v_traceState_944_);
lean_inc(v_auxDeclNGen_943_);
lean_inc(v_ngen_942_);
lean_inc(v_nextMacroScope_941_);
lean_inc(v_env_940_);
lean_dec(v___x_937_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
lean_inc(v_openDecls_939_);
lean_inc(v_currNamespace_938_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_currNamespace_938_);
lean_ctor_set(v___x_952_, 1, v_openDecls_939_);
v___x_953_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v___y_932_);
lean_inc_ref(v___y_933_);
lean_inc_ref(v___y_929_);
v___x_954_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_954_, 0, v___y_929_);
lean_ctor_set(v___x_954_, 1, v___y_928_);
lean_ctor_set(v___x_954_, 2, v___y_931_);
lean_ctor_set(v___x_954_, 3, v___y_933_);
lean_ctor_set(v___x_954_, 4, v___x_953_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*5, v___y_930_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*5 + 1, v___y_934_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*5 + 2, v_isSilent_921_);
v___x_955_ = l_Lean_MessageLog_add(v___x_954_, v_messages_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 6, v___x_955_);
v___x_957_ = v___x_950_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_env_940_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_nextMacroScope_941_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_ngen_942_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_auxDeclNGen_943_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_traceState_944_);
lean_ctor_set(v_reuseFailAlloc_961_, 5, v_cache_945_);
lean_ctor_set(v_reuseFailAlloc_961_, 6, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_961_, 7, v_infoState_947_);
lean_ctor_set(v_reuseFailAlloc_961_, 8, v_snapshotTasks_948_);
v___x_957_ = v_reuseFailAlloc_961_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_st_ref_set(v___y_936_, v___x_957_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
v___jp_963_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v___x_972_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_919_);
v___x_973_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_972_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_987_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc_ref_n(v___y_967_, 2);
v___x_978_ = l_Lean_FileMap_toPosition(v___y_967_, v___y_966_);
lean_dec(v___y_966_);
v___x_979_ = l_Lean_FileMap_toPosition(v___y_967_, v___y_971_);
lean_dec(v___y_971_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
v___x_981_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
if (v___y_969_ == 0)
{
lean_del_object(v___x_976_);
lean_dec_ref(v___y_964_);
v___y_928_ = v___x_978_;
v___y_929_ = v___y_965_;
v___y_930_ = v___y_968_;
v___y_931_ = v___x_980_;
v___y_932_ = v_a_974_;
v___y_933_ = v___x_981_;
v___y_934_ = v___y_970_;
v___y_935_ = v___y_924_;
v___y_936_ = v___y_925_;
goto v___jp_927_;
}
else
{
uint8_t v___x_982_; 
lean_inc(v_a_974_);
v___x_982_ = l_Lean_MessageData_hasTag(v___y_964_, v_a_974_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_985_; 
lean_dec_ref_known(v___x_980_, 1);
lean_dec_ref(v___x_978_);
lean_dec(v_a_974_);
v___x_983_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_983_);
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
else
{
lean_del_object(v___x_976_);
v___y_928_ = v___x_978_;
v___y_929_ = v___y_965_;
v___y_930_ = v___y_968_;
v___y_931_ = v___x_980_;
v___y_932_ = v_a_974_;
v___y_933_ = v___x_981_;
v___y_934_ = v___y_970_;
v___y_935_ = v___y_924_;
v___y_936_ = v___y_925_;
goto v___jp_927_;
}
}
}
}
v___jp_988_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_Syntax_getTailPos_x3f(v___y_991_, v___y_993_);
lean_dec(v___y_991_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_inc(v___y_996_);
v___y_964_ = v___y_989_;
v___y_965_ = v___y_990_;
v___y_966_ = v___y_996_;
v___y_967_ = v___y_992_;
v___y_968_ = v___y_993_;
v___y_969_ = v___y_994_;
v___y_970_ = v___y_995_;
v___y_971_ = v___y_996_;
goto v___jp_963_;
}
else
{
lean_object* v_val_998_; 
v_val_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_997_, 1);
v___y_964_ = v___y_989_;
v___y_965_ = v___y_990_;
v___y_966_ = v___y_996_;
v___y_967_ = v___y_992_;
v___y_968_ = v___y_993_;
v___y_969_ = v___y_994_;
v___y_970_ = v___y_995_;
v___y_971_ = v_val_998_;
goto v___jp_963_;
}
}
v___jp_999_:
{
lean_object* v_ref_1007_; lean_object* v___x_1008_; 
v_ref_1007_ = l_Lean_replaceRef(v_ref_918_, v___y_1001_);
v___x_1008_ = l_Lean_Syntax_getPos_x3f(v_ref_1007_, v___y_1004_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___y_989_ = v___y_1000_;
v___y_990_ = v___y_1002_;
v___y_991_ = v_ref_1007_;
v___y_992_ = v___y_1003_;
v___y_993_ = v___y_1004_;
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1006_;
v___y_996_ = v___x_1009_;
goto v___jp_988_;
}
else
{
lean_object* v_val_1010_; 
v_val_1010_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v___x_1008_, 1);
v___y_989_ = v___y_1000_;
v___y_990_ = v___y_1002_;
v___y_991_ = v_ref_1007_;
v___y_992_ = v___y_1003_;
v___y_993_ = v___y_1004_;
v___y_994_ = v___y_1005_;
v___y_995_ = v___y_1006_;
v___y_996_ = v_val_1010_;
goto v___jp_988_;
}
}
v___jp_1012_:
{
if (v___y_1019_ == 0)
{
v___y_1000_ = v___y_1015_;
v___y_1001_ = v___y_1013_;
v___y_1002_ = v___y_1014_;
v___y_1003_ = v___y_1016_;
v___y_1004_ = v___y_1018_;
v___y_1005_ = v___y_1017_;
v___y_1006_ = v_severity_920_;
goto v___jp_999_;
}
else
{
v___y_1000_ = v___y_1015_;
v___y_1001_ = v___y_1013_;
v___y_1002_ = v___y_1014_;
v___y_1003_ = v___y_1016_;
v___y_1004_ = v___y_1018_;
v___y_1005_ = v___y_1017_;
v___y_1006_ = v___x_1011_;
goto v___jp_999_;
}
}
v___jp_1020_:
{
if (v___y_1021_ == 0)
{
lean_object* v_fileName_1022_; lean_object* v_fileMap_1023_; lean_object* v_options_1024_; lean_object* v_ref_1025_; uint8_t v_suppressElabErrors_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; 
v_fileName_1022_ = lean_ctor_get(v___y_924_, 0);
v_fileMap_1023_ = lean_ctor_get(v___y_924_, 1);
v_options_1024_ = lean_ctor_get(v___y_924_, 2);
v_ref_1025_ = lean_ctor_get(v___y_924_, 5);
v_suppressElabErrors_1026_ = lean_ctor_get_uint8(v___y_924_, sizeof(void*)*14 + 1);
v___x_1027_ = lean_box(v___y_1021_);
v___x_1028_ = lean_box(v_suppressElabErrors_1026_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1029_, 0, v___x_1027_);
lean_closure_set(v___f_1029_, 1, v___x_1028_);
v___x_1030_ = 1;
v___x_1031_ = l_Lean_instBEqMessageSeverity_beq(v_severity_920_, v___x_1030_);
if (v___x_1031_ == 0)
{
v___y_1013_ = v_ref_1025_;
v___y_1014_ = v_fileName_1022_;
v___y_1015_ = v___f_1029_;
v___y_1016_ = v_fileMap_1023_;
v___y_1017_ = v_suppressElabErrors_1026_;
v___y_1018_ = v___y_1021_;
v___y_1019_ = v___x_1031_;
goto v___jp_1012_;
}
else
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = l_Lean_warningAsError;
v___x_1033_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1024_, v___x_1032_);
v___y_1013_ = v_ref_1025_;
v___y_1014_ = v_fileName_1022_;
v___y_1015_ = v___f_1029_;
v___y_1016_ = v_fileMap_1023_;
v___y_1017_ = v_suppressElabErrors_1026_;
v___y_1018_ = v___y_1021_;
v___y_1019_ = v___x_1033_;
goto v___jp_1012_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v_msgData_919_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1038_, lean_object* v_msgData_1039_, lean_object* v_severity_1040_, lean_object* v_isSilent_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
uint8_t v_severity_boxed_1047_; uint8_t v_isSilent_boxed_1048_; lean_object* v_res_1049_; 
v_severity_boxed_1047_ = lean_unbox(v_severity_1040_);
v_isSilent_boxed_1048_ = lean_unbox(v_isSilent_1041_);
v_res_1049_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1038_, v_msgData_1039_, v_severity_boxed_1047_, v_isSilent_boxed_1048_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v_ref_1038_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1050_, size_t v_sz_1051_, size_t v_i_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_usize_dec_lt(v_i_1052_, v_sz_1051_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1053_);
return v___x_1062_;
}
else
{
lean_object* v_ref_1063_; lean_object* v_a_1064_; uint8_t v_severity_1065_; uint8_t v_isSilent_1066_; lean_object* v_data_1067_; lean_object* v___x_1068_; 
v_ref_1063_ = lean_ctor_get(v___y_1058_, 5);
v_a_1064_ = lean_array_uget_borrowed(v_as_1050_, v_i_1052_);
v_severity_1065_ = lean_ctor_get_uint8(v_a_1064_, sizeof(void*)*5 + 1);
v_isSilent_1066_ = lean_ctor_get_uint8(v_a_1064_, sizeof(void*)*5 + 2);
v_data_1067_ = lean_ctor_get(v_a_1064_, 4);
lean_inc(v_data_1067_);
v___x_1068_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1063_, v_data_1067_, v_severity_1065_, v_isSilent_1066_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; 
lean_dec_ref_known(v___x_1068_, 1);
v___x_1069_ = lean_box(0);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1052_, v___x_1070_);
v_i_1052_ = v___x_1071_;
v_b_1053_ = v___x_1069_;
goto _start;
}
else
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1073_, lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
size_t v_sz_boxed_1084_; size_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_sz_boxed_1084_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1085_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1073_, v_sz_boxed_1084_, v_i_boxed_1085_, v_b_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v_as_1073_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v_infoState_1091_; lean_object* v_env_1092_; lean_object* v_nextMacroScope_1093_; lean_object* v_ngen_1094_; lean_object* v_auxDeclNGen_1095_; lean_object* v_traceState_1096_; lean_object* v_cache_1097_; lean_object* v_messages_1098_; lean_object* v_snapshotTasks_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1119_; 
v___x_1090_ = lean_st_ref_take(v___y_1088_);
v_infoState_1091_ = lean_ctor_get(v___x_1090_, 7);
v_env_1092_ = lean_ctor_get(v___x_1090_, 0);
v_nextMacroScope_1093_ = lean_ctor_get(v___x_1090_, 1);
v_ngen_1094_ = lean_ctor_get(v___x_1090_, 2);
v_auxDeclNGen_1095_ = lean_ctor_get(v___x_1090_, 3);
v_traceState_1096_ = lean_ctor_get(v___x_1090_, 4);
v_cache_1097_ = lean_ctor_get(v___x_1090_, 5);
v_messages_1098_ = lean_ctor_get(v___x_1090_, 6);
v_snapshotTasks_1099_ = lean_ctor_get(v___x_1090_, 8);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1101_ = v___x_1090_;
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snapshotTasks_1099_);
lean_inc(v_infoState_1091_);
lean_inc(v_messages_1098_);
lean_inc(v_cache_1097_);
lean_inc(v_traceState_1096_);
lean_inc(v_auxDeclNGen_1095_);
lean_inc(v_ngen_1094_);
lean_inc(v_nextMacroScope_1093_);
lean_inc(v_env_1092_);
lean_dec(v___x_1090_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_assignment_1103_; lean_object* v_lazyAssignment_1104_; lean_object* v_trees_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1118_; 
v_assignment_1103_ = lean_ctor_get(v_infoState_1091_, 0);
v_lazyAssignment_1104_ = lean_ctor_get(v_infoState_1091_, 1);
v_trees_1105_ = lean_ctor_get(v_infoState_1091_, 2);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_infoState_1091_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1107_ = v_infoState_1091_;
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_trees_1105_);
lean_inc(v_lazyAssignment_1104_);
lean_inc(v_assignment_1103_);
lean_dec(v_infoState_1091_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1118_;
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
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_assignment_1103_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_lazyAssignment_1104_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_trees_1105_);
v___x_1110_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*3, v_flag_1087_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 7, v___x_1110_);
v___x_1112_ = v___x_1101_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_env_1092_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_nextMacroScope_1093_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_ngen_1094_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_auxDeclNGen_1095_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_traceState_1096_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_cache_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 6, v_messages_1098_);
lean_ctor_set(v_reuseFailAlloc_1116_, 7, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1116_, 8, v_snapshotTasks_1099_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_st_ref_set(v___y_1088_, v___x_1112_);
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
uint8_t v_flag_boxed_1123_; lean_object* v_res_1124_; 
v_flag_boxed_1123_ = lean_unbox(v_flag_1120_);
v_res_1124_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1123_, v___y_1121_);
lean_dec(v___y_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_infoState_1135_; uint8_t v_enabled_1136_; lean_object* v_a_1138_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1134_ = lean_st_ref_get(v___y_1132_);
v_infoState_1135_ = lean_ctor_get(v___x_1134_, 7);
lean_inc_ref(v_infoState_1135_);
lean_dec(v___x_1134_);
v_enabled_1136_ = lean_ctor_get_uint8(v_infoState_1135_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1135_);
v___x_1148_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1125_, v___y_1132_);
lean_dec_ref(v___x_1148_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v___y_1128_);
lean_inc_ref(v___y_1127_);
v___x_1149_ = lean_apply_7(v_x_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, lean_box(0));
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1136_, v___y_1132_);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___x_1151_, 0);
lean_dec(v_unused_1159_);
v___x_1153_ = v___x_1151_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v___x_1151_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_a_1150_);
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1150_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1149_, 1);
v_a_1138_ = v_a_1160_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v___x_1139_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1136_, v___y_1132_);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v___x_1139_, 0);
lean_dec(v_unused_1147_);
v___x_1141_ = v___x_1139_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v___x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 0, v_a_1138_);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1138_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
uint8_t v_flag_boxed_1170_; lean_object* v_res_1171_; 
v_flag_boxed_1170_ = lean_unbox(v_flag_1161_);
v_res_1171_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1170_, v_x_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1172_, lean_object* v_binders_1173_, lean_object* v_blocks_1174_, lean_object* v_fileMap_x3f_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_a_1186_; size_t v_sz_1204_; size_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___y_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v_sz_1204_ = lean_array_size(v_blocks_1174_);
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1204_, v___x_1205_, v_blocks_1174_);
v___x_1207_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1207_, 0, v___x_1206_);
v___x_1208_ = 1;
v___x_1209_ = lean_box(v___x_1208_);
v___y_1210_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1210_, 0, v_fileMap_x3f_1175_);
lean_closure_set(v___y_1210_, 1, v_declName_1172_);
lean_closure_set(v___y_1210_, 2, v_binders_1173_);
lean_closure_set(v___y_1210_, 3, v___x_1207_);
lean_closure_set(v___y_1210_, 4, v___x_1209_);
v___x_1211_ = 0;
v___x_1212_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1211_, v___y_1210_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1181_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_Core_setMessageLog___redArg(v_a_1184_, v_a_1181_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v___x_1217_; lean_object* v___x_1218_; size_t v_sz_1219_; lean_object* v___x_1220_; 
lean_dec_ref_known(v___x_1216_, 1);
v___x_1217_ = l_Lean_MessageLog_toArray(v_a_1215_);
lean_dec(v_a_1215_);
v___x_1218_ = lean_box(0);
v_sz_1219_ = lean_array_size(v___x_1217_);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1217_, v_sz_1219_, v___x_1205_, v___x_1218_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec_ref(v___x_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1220_, 0);
lean_dec(v_unused_1246_);
v___x_1222_ = v___x_1220_;
v_isShared_1223_ = v_isSharedCheck_1245_;
goto v_resetjp_1221_;
}
else
{
lean_dec(v___x_1220_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1245_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1244_; 
v_fst_1224_ = lean_ctor_get(v_a_1213_, 0);
v_snd_1225_ = lean_ctor_get(v_a_1213_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_a_1213_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1227_ = v_a_1213_;
v_isShared_1228_ = v_isSharedCheck_1244_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_snd_1225_);
lean_inc(v_fst_1224_);
lean_dec(v_a_1213_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1244_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1243_; 
v_fst_1229_ = lean_ctor_get(v_fst_1224_, 0);
v_snd_1230_ = lean_ctor_get(v_fst_1224_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_fst_1224_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1232_ = v_fst_1224_;
v_isShared_1233_ = v_isSharedCheck_1243_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_fst_1224_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1243_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_fst_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_snd_1230_);
v___x_1235_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1235_);
v___x_1237_ = v___x_1227_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_snd_1225_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1237_);
v___x_1239_ = v___x_1222_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec(v_a_1213_);
v_a_1247_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1220_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1220_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_a_1215_);
lean_dec(v_a_1213_);
v_a_1255_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1216_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1216_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; 
lean_dec(v_a_1213_);
v_a_1263_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1214_, 1);
v_a_1186_ = v_a_1263_;
goto v___jp_1185_;
}
}
else
{
lean_object* v_a_1264_; 
v_a_1264_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1212_, 1);
v_a_1186_ = v_a_1264_;
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Core_setMessageLog___redArg(v_a_1184_, v_a_1181_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1195_);
v___x_1189_ = v___x_1187_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 1);
lean_ctor_set(v___x_1189_, 0, v_a_1186_);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1186_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_a_1186_);
v_a_1196_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1187_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1187_);
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
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_fileMap_x3f_1175_);
lean_dec_ref(v_blocks_1174_);
lean_dec(v_binders_1173_);
lean_dec(v_declName_1172_);
v_a_1265_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1183_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1183_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1273_, lean_object* v_binders_1274_, lean_object* v_blocks_1275_, lean_object* v_fileMap_x3f_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1273_, v_binders_1274_, v_blocks_1275_, v_fileMap_x3f_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1285_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_flag_boxed_1302_; lean_object* v_res_1303_; 
v_flag_boxed_1302_ = lean_unbox(v_flag_1294_);
v_res_1303_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1302_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1304_, uint8_t v_flag_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1305_, v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1315_, lean_object* v_flag_1316_, lean_object* v_x_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
uint8_t v_flag_boxed_1325_; lean_object* v_res_1326_; 
v_flag_boxed_1325_ = lean_unbox(v_flag_1316_);
v_res_1326_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1315_, v_flag_boxed_1325_, v_x_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1327_, lean_object* v_msgData_1328_, uint8_t v_severity_1329_, uint8_t v_isSilent_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1327_, v_msgData_1328_, v_severity_1329_, v_isSilent_1330_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1339_, lean_object* v_msgData_1340_, lean_object* v_severity_1341_, lean_object* v_isSilent_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
uint8_t v_severity_boxed_1350_; uint8_t v_isSilent_boxed_1351_; lean_object* v_res_1352_; 
v_severity_boxed_1350_ = lean_unbox(v_severity_1341_);
v_isSilent_boxed_1351_ = lean_unbox(v_isSilent_1342_);
v_res_1352_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1339_, v_msgData_1340_, v_severity_boxed_1350_, v_isSilent_boxed_1351_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v_ref_1339_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1353_, uint8_t v_severity_1354_, uint8_t v_isSilent_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_ref_1361_; lean_object* v___x_1362_; 
v_ref_1361_ = lean_ctor_get(v___y_1358_, 5);
v___x_1362_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1361_, v_msgData_1353_, v_severity_1354_, v_isSilent_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1363_, lean_object* v_severity_1364_, lean_object* v_isSilent_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
uint8_t v_severity_boxed_1371_; uint8_t v_isSilent_boxed_1372_; lean_object* v_res_1373_; 
v_severity_boxed_1371_ = lean_unbox(v_severity_1364_);
v_isSilent_boxed_1372_ = lean_unbox(v_isSilent_1365_);
v_res_1373_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1363_, v_severity_boxed_1371_, v_isSilent_boxed_1372_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = 2;
v___x_1383_ = 0;
v___x_1384_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1374_, v___x_1382_, v___x_1383_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1394_, size_t v_sz_1395_, size_t v_i_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_usize_dec_lt(v_i_1396_, v_sz_1395_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_b_1397_);
return v___x_1406_;
}
else
{
lean_object* v_a_1407_; lean_object* v_snd_1408_; lean_object* v_snd_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_a_1407_ = lean_array_uget_borrowed(v_as_1394_, v_i_1396_);
v_snd_1408_ = lean_ctor_get(v_a_1407_, 1);
v_snd_1409_ = lean_ctor_get(v_snd_1408_, 1);
lean_inc(v_snd_1409_);
v___x_1410_ = l_Lean_Parser_Error_toString(v_snd_1409_);
v___x_1411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
v___x_1412_ = l_Lean_MessageData_ofFormat(v___x_1411_);
v___x_1413_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1412_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; size_t v___x_1415_; size_t v___x_1416_; 
lean_dec_ref_known(v___x_1413_, 1);
v___x_1414_ = lean_box(0);
v___x_1415_ = ((size_t)1ULL);
v___x_1416_ = lean_usize_add(v_i_1396_, v___x_1415_);
v_i_1396_ = v___x_1416_;
v_b_1397_ = v___x_1414_;
goto _start;
}
else
{
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1418_, lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_b_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
size_t v_sz_boxed_1429_; size_t v_i_boxed_1430_; lean_object* v_res_1431_; 
v_sz_boxed_1429_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1430_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1418_, v_sz_boxed_1429_, v_i_boxed_1430_, v_b_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_as_1418_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1449_, lean_object* v_binders_1450_, lean_object* v_docComment_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v_env_1460_; lean_object* v_fileName_1461_; lean_object* v_options_1462_; lean_object* v_currNamespace_1463_; lean_object* v_openDecls_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1459_ = lean_st_ref_get(v_a_1457_);
v_env_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc_ref_n(v_env_1460_, 2);
lean_dec(v___x_1459_);
v_fileName_1461_ = lean_ctor_get(v_a_1456_, 0);
v_options_1462_ = lean_ctor_get(v_a_1456_, 2);
v_currNamespace_1463_ = lean_ctor_get(v_a_1456_, 6);
v_openDecls_1464_ = lean_ctor_get(v_a_1456_, 7);
v___x_1465_ = lean_string_utf8_byte_size(v_docComment_1451_);
lean_inc_ref_n(v_docComment_1451_, 2);
v___x_1466_ = l_Lean_FileMap_ofString(v_docComment_1451_);
lean_inc_ref(v___x_1466_);
lean_inc_ref(v_fileName_1461_);
v___x_1467_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1467_, 0, v_docComment_1451_);
lean_ctor_set(v___x_1467_, 1, v_fileName_1461_);
lean_ctor_set(v___x_1467_, 2, v___x_1466_);
lean_ctor_set(v___x_1467_, 3, v___x_1465_);
lean_inc(v_openDecls_1464_);
lean_inc(v_currNamespace_1463_);
lean_inc_ref(v_options_1462_);
v___x_1468_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1468_, 0, v_env_1460_);
lean_ctor_set(v___x_1468_, 1, v_options_1462_);
lean_ctor_set(v___x_1468_, 2, v_currNamespace_1463_);
lean_ctor_set(v___x_1468_, 3, v_openDecls_1464_);
v___x_1469_ = l_Lean_Parser_mkParserState(v_docComment_1451_);
lean_dec_ref(v_docComment_1451_);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1472_ = l_Lean_Parser_getTokenTable(v_env_1460_);
v___x_1473_ = l_Lean_Parser_ParserFn_run(v___x_1471_, v___x_1467_, v___x_1468_, v___x_1472_, v___x_1469_);
lean_inc_ref(v___x_1473_);
v___x_1474_ = l_Lean_Parser_ParserState_allErrors(v___x_1473_);
v___x_1475_ = lean_array_get_size(v___x_1474_);
v___x_1476_ = lean_nat_dec_eq(v___x_1475_, v___x_1470_);
v___x_1477_ = lean_bool_not(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v_stxStack_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec_ref(v___x_1474_);
v_stxStack_1478_ = lean_ctor_get(v___x_1473_, 0);
lean_inc_ref(v_stxStack_1478_);
lean_dec_ref(v___x_1473_);
v___x_1479_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1478_);
lean_dec_ref(v_stxStack_1478_);
v___x_1480_ = l_Lean_Syntax_getArgs(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1466_);
v___x_1482_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1449_, v_binders_1450_, v___x_1480_, v___x_1481_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1466_);
lean_dec(v_binders_1450_);
lean_dec(v_declName_1449_);
v___x_1483_ = lean_box(0);
v_sz_1484_ = lean_array_size(v___x_1474_);
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1474_, v_sz_1484_, v___x_1485_, v___x_1483_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec_ref(v___x_1474_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1495_);
v___x_1488_ = v___x_1486_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_dec(v___x_1486_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1486_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1486_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1504_, lean_object* v_binders_1505_, lean_object* v_docComment_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_versoDocStringOfText(v_declName_1504_, v_binders_1505_, v_docComment_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1515_, uint8_t v_severity_1516_, uint8_t v_isSilent_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1515_, v_severity_1516_, v_isSilent_1517_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1526_, lean_object* v_severity_1527_, lean_object* v_isSilent_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v_severity_boxed_1536_; uint8_t v_isSilent_boxed_1537_; lean_object* v_res_1538_; 
v_severity_boxed_1536_ = lean_unbox(v_severity_1527_);
v_isSilent_boxed_1537_ = lean_unbox(v_isSilent_1528_);
v_res_1538_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1526_, v_severity_boxed_1536_, v_isSilent_boxed_1537_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_1539_, size_t v_i_1540_, lean_object* v_bs_1541_){
_start:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_usize_dec_lt(v_i_1540_, v_sz_1539_);
if (v___x_1542_ == 0)
{
return v_bs_1541_;
}
else
{
lean_object* v_v_1543_; lean_object* v___x_1544_; lean_object* v_bs_x27_1545_; size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v_v_1543_ = lean_array_uget(v_bs_1541_, v_i_1540_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v_bs_x27_1545_ = lean_array_uset(v_bs_1541_, v_i_1540_, v___x_1544_);
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1540_, v___x_1546_);
v___x_1548_ = lean_array_uset(v_bs_x27_1545_, v_i_1540_, v_v_1543_);
v_i_1540_ = v___x_1547_;
v_bs_1541_ = v___x_1548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_1550_, lean_object* v_i_1551_, lean_object* v_bs_1552_){
_start:
{
size_t v_sz_boxed_1553_; size_t v_i_boxed_1554_; lean_object* v_res_1555_; 
v_sz_boxed_1553_ = lean_unbox_usize(v_sz_1550_);
lean_dec(v_sz_1550_);
v_i_boxed_1554_ = lean_unbox_usize(v_i_1551_);
lean_dec(v_i_1551_);
v_res_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_1553_, v_i_boxed_1554_, v_bs_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v___x_1556_, uint8_t v_suppressElabErrors_1557_, lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 1)
{
lean_object* v_pre_1559_; 
v_pre_1559_ = lean_ctor_get(v_x_1558_, 0);
switch(lean_obj_tag(v_pre_1559_))
{
case 1:
{
lean_object* v_pre_1560_; 
v_pre_1560_ = lean_ctor_get(v_pre_1559_, 0);
switch(lean_obj_tag(v_pre_1560_))
{
case 0:
{
lean_object* v_str_1561_; lean_object* v_str_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_str_1561_ = lean_ctor_get(v_x_1558_, 1);
v_str_1562_ = lean_ctor_get(v_pre_1559_, 1);
v___x_1563_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1564_ = lean_string_dec_eq(v_str_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1566_ = lean_string_dec_eq(v_str_1562_, v___x_1565_);
if (v___x_1566_ == 0)
{
return v___x_1556_;
}
else
{
lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1567_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1568_ = lean_string_dec_eq(v_str_1561_, v___x_1567_);
if (v___x_1568_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1557_;
}
}
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1570_ = lean_string_dec_eq(v_str_1561_, v___x_1569_);
if (v___x_1570_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1557_;
}
}
}
case 1:
{
lean_object* v_pre_1571_; 
v_pre_1571_ = lean_ctor_get(v_pre_1560_, 0);
if (lean_obj_tag(v_pre_1571_) == 0)
{
lean_object* v_str_1572_; lean_object* v_str_1573_; lean_object* v_str_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_str_1572_ = lean_ctor_get(v_x_1558_, 1);
v_str_1573_ = lean_ctor_get(v_pre_1559_, 1);
v_str_1574_ = lean_ctor_get(v_pre_1560_, 1);
v___x_1575_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1576_ = lean_string_dec_eq(v_str_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
return v___x_1556_;
}
else
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1578_ = lean_string_dec_eq(v_str_1573_, v___x_1577_);
if (v___x_1578_ == 0)
{
return v___x_1556_;
}
else
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1580_ = lean_string_dec_eq(v_str_1572_, v___x_1579_);
if (v___x_1580_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1557_;
}
}
}
}
else
{
return v___x_1556_;
}
}
default: 
{
return v___x_1556_;
}
}
}
case 0:
{
lean_object* v_str_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_str_1581_ = lean_ctor_get(v_x_1558_, 1);
v___x_1582_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1583_ = lean_string_dec_eq(v_str_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
return v___x_1556_;
}
else
{
return v_suppressElabErrors_1557_;
}
}
default: 
{
return v___x_1556_;
}
}
}
else
{
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v___x_1584_, lean_object* v_suppressElabErrors_1585_, lean_object* v_x_1586_){
_start:
{
uint8_t v___x_11395__boxed_1587_; uint8_t v_suppressElabErrors_boxed_1588_; uint8_t v_res_1589_; lean_object* v_r_1590_; 
v___x_11395__boxed_1587_ = lean_unbox(v___x_1584_);
v_suppressElabErrors_boxed_1588_ = lean_unbox(v_suppressElabErrors_1585_);
v_res_1589_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_11395__boxed_1587_, v_suppressElabErrors_boxed_1588_, v_x_1586_);
lean_dec(v_x_1586_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v___x_1591_, uint8_t v_suppressElabErrors_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 1)
{
lean_object* v_pre_1594_; 
v_pre_1594_ = lean_ctor_get(v_x_1593_, 0);
switch(lean_obj_tag(v_pre_1594_))
{
case 1:
{
lean_object* v_pre_1595_; 
v_pre_1595_ = lean_ctor_get(v_pre_1594_, 0);
switch(lean_obj_tag(v_pre_1595_))
{
case 0:
{
lean_object* v_str_1596_; lean_object* v_str_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_str_1596_ = lean_ctor_get(v_x_1593_, 1);
v_str_1597_ = lean_ctor_get(v_pre_1594_, 1);
v___x_1598_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1599_ = lean_string_dec_eq(v_str_1597_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1601_ = lean_string_dec_eq(v_str_1597_, v___x_1600_);
if (v___x_1601_ == 0)
{
return v___x_1591_;
}
else
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1603_ = lean_string_dec_eq(v_str_1596_, v___x_1602_);
if (v___x_1603_ == 0)
{
return v___x_1591_;
}
else
{
return v_suppressElabErrors_1592_;
}
}
}
else
{
lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1605_ = lean_string_dec_eq(v_str_1596_, v___x_1604_);
if (v___x_1605_ == 0)
{
return v___x_1591_;
}
else
{
return v_suppressElabErrors_1592_;
}
}
}
case 1:
{
lean_object* v_pre_1606_; 
v_pre_1606_ = lean_ctor_get(v_pre_1595_, 0);
if (lean_obj_tag(v_pre_1606_) == 0)
{
lean_object* v_str_1607_; lean_object* v_str_1608_; lean_object* v_str_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_str_1607_ = lean_ctor_get(v_x_1593_, 1);
v_str_1608_ = lean_ctor_get(v_pre_1594_, 1);
v_str_1609_ = lean_ctor_get(v_pre_1595_, 1);
v___x_1610_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1611_ = lean_string_dec_eq(v_str_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
return v___x_1591_;
}
else
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1613_ = lean_string_dec_eq(v_str_1608_, v___x_1612_);
if (v___x_1613_ == 0)
{
return v___x_1591_;
}
else
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1615_ = lean_string_dec_eq(v_str_1607_, v___x_1614_);
if (v___x_1615_ == 0)
{
return v___x_1591_;
}
else
{
return v_suppressElabErrors_1592_;
}
}
}
}
else
{
return v___x_1591_;
}
}
default: 
{
return v___x_1591_;
}
}
}
case 0:
{
lean_object* v_str_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_str_1616_ = lean_ctor_get(v_x_1593_, 1);
v___x_1617_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1618_ = lean_string_dec_eq(v_str_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
return v___x_1591_;
}
else
{
return v_suppressElabErrors_1592_;
}
}
default: 
{
return v___x_1591_;
}
}
}
else
{
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___x_1619_, lean_object* v_suppressElabErrors_1620_, lean_object* v_x_1621_){
_start:
{
uint8_t v___x_11459__boxed_1622_; uint8_t v_suppressElabErrors_boxed_1623_; uint8_t v_res_1624_; lean_object* v_r_1625_; 
v___x_11459__boxed_1622_ = lean_unbox(v___x_1619_);
v_suppressElabErrors_boxed_1623_ = lean_unbox(v_suppressElabErrors_1620_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_11459__boxed_1622_, v_suppressElabErrors_boxed_1623_, v_x_1621_);
lean_dec(v_x_1621_);
v_r_1625_ = lean_box(v_res_1624_);
return v_r_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_1626_, lean_object* v_as_1627_, size_t v_sz_1628_, size_t v_i_1629_, lean_object* v_b_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_a_1635_; uint8_t v___x_1639_; 
v___x_1639_ = lean_usize_dec_lt(v_i_1629_, v_sz_1628_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec_ref(v___x_1626_);
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_b_1630_);
return v___x_1640_;
}
else
{
lean_object* v_a_1641_; lean_object* v_snd_1642_; lean_object* v_fst_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1699_; 
v_a_1641_ = lean_array_uget(v_as_1627_, v_i_1629_);
v_snd_1642_ = lean_ctor_get(v_a_1641_, 1);
v_fst_1643_ = lean_ctor_get(v_a_1641_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_a_1641_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1645_ = v_a_1641_;
v_isShared_1646_ = v_isSharedCheck_1699_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snd_1642_);
lean_inc(v_fst_1643_);
lean_dec(v_a_1641_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1699_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_snd_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1697_; 
v_snd_1647_ = lean_ctor_get(v_snd_1642_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_snd_1642_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_snd_1642_, 0);
lean_dec(v_unused_1698_);
v___x_1649_ = v_snd_1642_;
v_isShared_1650_ = v_isSharedCheck_1697_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_snd_1647_);
lean_dec(v_snd_1642_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1697_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fileName_1651_; uint8_t v_suppressElabErrors_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___y_1663_; lean_object* v___y_1664_; 
v_fileName_1651_ = lean_ctor_get(v___y_1631_, 0);
v_suppressElabErrors_1652_ = lean_ctor_get_uint8(v___y_1631_, sizeof(void*)*14 + 1);
v___x_1653_ = lean_box(0);
lean_inc_ref(v___x_1626_);
v___x_1654_ = l_Lean_FileMap_toPosition(v___x_1626_, v_fst_1643_);
lean_dec(v_fst_1643_);
v___x_1655_ = lean_box(0);
v___x_1656_ = 0;
v___x_1657_ = 2;
v___x_1658_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
v___x_1659_ = l_Lean_Parser_Error_toString(v_snd_1647_);
v___x_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = l_Lean_MessageData_ofFormat(v___x_1660_);
if (v_suppressElabErrors_1652_ == 0)
{
v___y_1663_ = v___y_1631_;
v___y_1664_ = v___y_1632_;
goto v___jp_1662_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___f_1695_; uint8_t v___x_1696_; 
v___x_1693_ = lean_box(v___x_1656_);
v___x_1694_ = lean_box(v_suppressElabErrors_1652_);
v___f_1695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1695_, 0, v___x_1693_);
lean_closure_set(v___f_1695_, 1, v___x_1694_);
lean_inc_ref(v___x_1661_);
v___x_1696_ = l_Lean_MessageData_hasTag(v___f_1695_, v___x_1661_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v___x_1661_);
lean_dec_ref(v___x_1654_);
lean_del_object(v___x_1649_);
lean_del_object(v___x_1645_);
v_a_1635_ = v___x_1653_;
goto v___jp_1634_;
}
else
{
v___y_1663_ = v___y_1631_;
v___y_1664_ = v___y_1632_;
goto v___jp_1662_;
}
}
v___jp_1662_:
{
lean_object* v___x_1665_; lean_object* v_currNamespace_1666_; lean_object* v_openDecls_1667_; lean_object* v___x_1669_; 
v___x_1665_ = lean_st_ref_take(v___y_1664_);
v_currNamespace_1666_ = lean_ctor_get(v___y_1663_, 6);
v_openDecls_1667_ = lean_ctor_get(v___y_1663_, 7);
lean_inc(v_openDecls_1667_);
lean_inc(v_currNamespace_1666_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v_openDecls_1667_);
lean_ctor_set(v___x_1649_, 0, v_currNamespace_1666_);
v___x_1669_ = v___x_1649_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_currNamespace_1666_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_openDecls_1667_);
v___x_1669_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 4);
lean_ctor_set(v___x_1645_, 1, v___x_1661_);
lean_ctor_set(v___x_1645_, 0, v___x_1669_);
v___x_1671_ = v___x_1645_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1661_);
v___x_1671_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v_env_1673_; lean_object* v_nextMacroScope_1674_; lean_object* v_ngen_1675_; lean_object* v_auxDeclNGen_1676_; lean_object* v_traceState_1677_; lean_object* v_cache_1678_; lean_object* v_messages_1679_; lean_object* v_infoState_1680_; lean_object* v_snapshotTasks_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1690_; 
lean_inc_ref(v_fileName_1651_);
v___x_1672_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1672_, 0, v_fileName_1651_);
lean_ctor_set(v___x_1672_, 1, v___x_1654_);
lean_ctor_set(v___x_1672_, 2, v___x_1655_);
lean_ctor_set(v___x_1672_, 3, v___x_1658_);
lean_ctor_set(v___x_1672_, 4, v___x_1671_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*5, v___x_1656_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*5 + 1, v___x_1657_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*5 + 2, v___x_1656_);
v_env_1673_ = lean_ctor_get(v___x_1665_, 0);
v_nextMacroScope_1674_ = lean_ctor_get(v___x_1665_, 1);
v_ngen_1675_ = lean_ctor_get(v___x_1665_, 2);
v_auxDeclNGen_1676_ = lean_ctor_get(v___x_1665_, 3);
v_traceState_1677_ = lean_ctor_get(v___x_1665_, 4);
v_cache_1678_ = lean_ctor_get(v___x_1665_, 5);
v_messages_1679_ = lean_ctor_get(v___x_1665_, 6);
v_infoState_1680_ = lean_ctor_get(v___x_1665_, 7);
v_snapshotTasks_1681_ = lean_ctor_get(v___x_1665_, 8);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1683_ = v___x_1665_;
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snapshotTasks_1681_);
lean_inc(v_infoState_1680_);
lean_inc(v_messages_1679_);
lean_inc(v_cache_1678_);
lean_inc(v_traceState_1677_);
lean_inc(v_auxDeclNGen_1676_);
lean_inc(v_ngen_1675_);
lean_inc(v_nextMacroScope_1674_);
lean_inc(v_env_1673_);
lean_dec(v___x_1665_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1690_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = l_Lean_MessageLog_add(v___x_1672_, v_messages_1679_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 6, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_env_1673_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_nextMacroScope_1674_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_ngen_1675_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_auxDeclNGen_1676_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_traceState_1677_);
lean_ctor_set(v_reuseFailAlloc_1689_, 5, v_cache_1678_);
lean_ctor_set(v_reuseFailAlloc_1689_, 6, v___x_1685_);
lean_ctor_set(v_reuseFailAlloc_1689_, 7, v_infoState_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 8, v_snapshotTasks_1681_);
v___x_1687_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; 
v___x_1688_ = lean_st_ref_set(v___y_1664_, v___x_1687_);
v_a_1635_ = v___x_1653_;
goto v___jp_1634_;
}
}
}
}
}
}
}
}
v___jp_1634_:
{
size_t v___x_1636_; size_t v___x_1637_; 
v___x_1636_ = ((size_t)1ULL);
v___x_1637_ = lean_usize_add(v_i_1629_, v___x_1636_);
v_i_1629_ = v___x_1637_;
v_b_1630_ = v_a_1635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1700_, lean_object* v_as_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1700_, v_as_1701_, v_sz_boxed_1708_, v_i_boxed_1709_, v_b_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec_ref(v_as_1701_);
return v_res_1710_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_box(1);
v___x_1712_ = l_Lean_MessageData_ofFormat(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
if (lean_obj_tag(v_x_1719_) == 0)
{
return v_x_1718_;
}
else
{
lean_object* v_head_1720_; lean_object* v_tail_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1743_; 
v_head_1720_ = lean_ctor_get(v_x_1719_, 0);
v_tail_1721_ = lean_ctor_get(v_x_1719_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_x_1719_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1723_ = v_x_1719_;
v_isShared_1724_ = v_isSharedCheck_1743_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_tail_1721_);
lean_inc(v_head_1720_);
lean_dec(v_x_1719_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1743_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_before_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1741_; 
v_before_1725_ = lean_ctor_get(v_head_1720_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_head_1720_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_head_1720_, 1);
lean_dec(v_unused_1742_);
v___x_1727_ = v_head_1720_;
v_isShared_1728_ = v_isSharedCheck_1741_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_before_1725_);
lean_dec(v_head_1720_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1741_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 7);
lean_ctor_set(v___x_1727_, 1, v___x_1729_);
lean_ctor_set(v___x_1727_, 0, v_x_1718_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_x_1718_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 7);
lean_ctor_set(v___x_1723_, 1, v___x_1732_);
lean_ctor_set(v___x_1723_, 0, v___x_1731_);
v___x_1734_ = v___x_1723_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = l_Lean_MessageData_ofSyntax(v_before_1725_);
v___x_1736_ = l_Lean_indentD(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1734_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v_x_1718_ = v___x_1737_;
v_x_1719_ = v_tail_1721_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1748_ = l_Lean_MessageData_ofFormat(v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1749_, lean_object* v_macroStack_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_options_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; 
v_options_1753_ = lean_ctor_get(v___y_1751_, 2);
v___x_1754_ = l_Lean_Elab_pp_macroStack;
v___x_1755_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1753_, v___x_1754_);
v___x_1756_ = lean_bool_not(v___x_1755_);
if (v___x_1756_ == 0)
{
if (lean_obj_tag(v_macroStack_1750_) == 0)
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_msgData_1749_);
return v___x_1757_;
}
else
{
lean_object* v_head_1758_; lean_object* v_after_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1774_; 
v_head_1758_ = lean_ctor_get(v_macroStack_1750_, 0);
lean_inc(v_head_1758_);
v_after_1759_ = lean_ctor_get(v_head_1758_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_head_1758_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_head_1758_, 0);
lean_dec(v_unused_1775_);
v___x_1761_ = v_head_1758_;
v_isShared_1762_ = v_isSharedCheck_1774_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_after_1759_);
lean_dec(v_head_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1774_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 7);
lean_ctor_set(v___x_1761_, 1, v___x_1763_);
lean_ctor_set(v___x_1761_, 0, v_msgData_1749_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_msgData_1749_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v_msgData_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1766_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = l_Lean_MessageData_ofSyntax(v_after_1759_);
v___x_1769_ = l_Lean_indentD(v___x_1768_);
v_msgData_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1770_, 0, v___x_1767_);
lean_ctor_set(v_msgData_1770_, 1, v___x_1769_);
v___x_1771_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1770_, v_macroStack_1750_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
}
}
}
else
{
lean_object* v___x_1776_; 
lean_dec(v_macroStack_1750_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_msgData_1749_);
return v___x_1776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1777_, lean_object* v_macroStack_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1777_, v_macroStack_1778_, v___y_1779_);
lean_dec_ref(v___y_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_ref_1790_; lean_object* v___x_1791_; lean_object* v_a_1792_; lean_object* v_macroStack_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1804_; 
v_ref_1790_ = lean_ctor_get(v___y_1787_, 5);
v___x_1791_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1782_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v_macroStack_1793_ = lean_ctor_get(v___y_1783_, 1);
v___x_1794_ = l_Lean_Elab_getBetterRef(v_ref_1790_, v_macroStack_1793_);
lean_inc(v_macroStack_1793_);
v___x_1795_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1792_, v_macroStack_1793_, v___y_1787_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1804_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1794_);
lean_ctor_set(v___x_1800_, 1, v_a_1796_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set_tag(v___x_1798_, 1);
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1802_ = v___x_1798_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1814_, lean_object* v_msg_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_fileName_1823_; lean_object* v_fileMap_1824_; lean_object* v_options_1825_; lean_object* v_currRecDepth_1826_; lean_object* v_maxRecDepth_1827_; lean_object* v_ref_1828_; lean_object* v_currNamespace_1829_; lean_object* v_openDecls_1830_; lean_object* v_initHeartbeats_1831_; lean_object* v_maxHeartbeats_1832_; lean_object* v_quotContext_1833_; lean_object* v_currMacroScope_1834_; uint8_t v_diag_1835_; lean_object* v_cancelTk_x3f_1836_; uint8_t v_suppressElabErrors_1837_; lean_object* v_inheritedTraceOptions_1838_; lean_object* v_ref_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v_fileName_1823_ = lean_ctor_get(v___y_1820_, 0);
v_fileMap_1824_ = lean_ctor_get(v___y_1820_, 1);
v_options_1825_ = lean_ctor_get(v___y_1820_, 2);
v_currRecDepth_1826_ = lean_ctor_get(v___y_1820_, 3);
v_maxRecDepth_1827_ = lean_ctor_get(v___y_1820_, 4);
v_ref_1828_ = lean_ctor_get(v___y_1820_, 5);
v_currNamespace_1829_ = lean_ctor_get(v___y_1820_, 6);
v_openDecls_1830_ = lean_ctor_get(v___y_1820_, 7);
v_initHeartbeats_1831_ = lean_ctor_get(v___y_1820_, 8);
v_maxHeartbeats_1832_ = lean_ctor_get(v___y_1820_, 9);
v_quotContext_1833_ = lean_ctor_get(v___y_1820_, 10);
v_currMacroScope_1834_ = lean_ctor_get(v___y_1820_, 11);
v_diag_1835_ = lean_ctor_get_uint8(v___y_1820_, sizeof(void*)*14);
v_cancelTk_x3f_1836_ = lean_ctor_get(v___y_1820_, 12);
v_suppressElabErrors_1837_ = lean_ctor_get_uint8(v___y_1820_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1838_ = lean_ctor_get(v___y_1820_, 13);
v_ref_1839_ = l_Lean_replaceRef(v_ref_1814_, v_ref_1828_);
lean_inc_ref(v_inheritedTraceOptions_1838_);
lean_inc(v_cancelTk_x3f_1836_);
lean_inc(v_currMacroScope_1834_);
lean_inc(v_quotContext_1833_);
lean_inc(v_maxHeartbeats_1832_);
lean_inc(v_initHeartbeats_1831_);
lean_inc(v_openDecls_1830_);
lean_inc(v_currNamespace_1829_);
lean_inc(v_maxRecDepth_1827_);
lean_inc(v_currRecDepth_1826_);
lean_inc_ref(v_options_1825_);
lean_inc_ref(v_fileMap_1824_);
lean_inc_ref(v_fileName_1823_);
v___x_1840_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1840_, 0, v_fileName_1823_);
lean_ctor_set(v___x_1840_, 1, v_fileMap_1824_);
lean_ctor_set(v___x_1840_, 2, v_options_1825_);
lean_ctor_set(v___x_1840_, 3, v_currRecDepth_1826_);
lean_ctor_set(v___x_1840_, 4, v_maxRecDepth_1827_);
lean_ctor_set(v___x_1840_, 5, v_ref_1839_);
lean_ctor_set(v___x_1840_, 6, v_currNamespace_1829_);
lean_ctor_set(v___x_1840_, 7, v_openDecls_1830_);
lean_ctor_set(v___x_1840_, 8, v_initHeartbeats_1831_);
lean_ctor_set(v___x_1840_, 9, v_maxHeartbeats_1832_);
lean_ctor_set(v___x_1840_, 10, v_quotContext_1833_);
lean_ctor_set(v___x_1840_, 11, v_currMacroScope_1834_);
lean_ctor_set(v___x_1840_, 12, v_cancelTk_x3f_1836_);
lean_ctor_set(v___x_1840_, 13, v_inheritedTraceOptions_1838_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*14, v_diag_1835_);
lean_ctor_set_uint8(v___x_1840_, sizeof(void*)*14 + 1, v_suppressElabErrors_1837_);
v___x_1841_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___x_1840_, v___y_1821_);
lean_dec_ref_known(v___x_1840_, 14);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1842_, lean_object* v_msg_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1842_, v_msg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_ref_1842_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; uint8_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; uint8_t v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; uint8_t v___y_1966_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; uint8_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
lean_inc(v_docComment_1852_);
v___x_2028_ = l_Lean_Syntax_getKind(v_docComment_1852_);
v___x_2029_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2030_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2031_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2032_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2033_ = lean_name_eq(v___x_2028_, v___x_2032_);
lean_dec(v___x_2028_);
if (v___x_2033_ == 0)
{
goto v___jp_2005_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_unsigned_to_nat(0u);
v___x_2035_ = l_Lean_Syntax_getArg(v_docComment_1852_, v___x_2034_);
if (lean_obj_tag(v___x_2035_) == 1)
{
lean_object* v_kind_2036_; 
v_kind_2036_ = lean_ctor_get(v___x_2035_, 1);
lean_inc(v_kind_2036_);
if (lean_obj_tag(v_kind_2036_) == 1)
{
lean_object* v_pre_2037_; 
v_pre_2037_ = lean_ctor_get(v_kind_2036_, 0);
lean_inc(v_pre_2037_);
if (lean_obj_tag(v_pre_2037_) == 1)
{
lean_object* v_pre_2038_; 
v_pre_2038_ = lean_ctor_get(v_pre_2037_, 0);
lean_inc(v_pre_2038_);
if (lean_obj_tag(v_pre_2038_) == 1)
{
lean_object* v_pre_2039_; 
v_pre_2039_ = lean_ctor_get(v_pre_2038_, 0);
lean_inc(v_pre_2039_);
if (lean_obj_tag(v_pre_2039_) == 1)
{
lean_object* v_pre_2040_; 
v_pre_2040_ = lean_ctor_get(v_pre_2039_, 0);
lean_inc(v_pre_2040_);
if (lean_obj_tag(v_pre_2040_) == 0)
{
lean_object* v_info_2041_; lean_object* v_args_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2068_; 
v_info_2041_ = lean_ctor_get(v___x_2035_, 0);
v_args_2042_ = lean_ctor_get(v___x_2035_, 2);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2035_, 1);
lean_dec(v_unused_2069_);
v___x_2044_ = v___x_2035_;
v_isShared_2045_ = v_isSharedCheck_2068_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_args_2042_);
lean_inc(v_info_2041_);
lean_dec(v___x_2035_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2068_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v_str_2046_; lean_object* v_str_2047_; lean_object* v_str_2048_; lean_object* v_str_2049_; uint8_t v___x_2050_; 
v_str_2046_ = lean_ctor_get(v_kind_2036_, 1);
lean_inc_ref(v_str_2046_);
lean_dec_ref_known(v_kind_2036_, 2);
v_str_2047_ = lean_ctor_get(v_pre_2037_, 1);
lean_inc_ref(v_str_2047_);
lean_dec_ref_known(v_pre_2037_, 2);
v_str_2048_ = lean_ctor_get(v_pre_2038_, 1);
lean_inc_ref(v_str_2048_);
lean_dec_ref_known(v_pre_2038_, 2);
v_str_2049_ = lean_ctor_get(v_pre_2039_, 1);
lean_inc_ref(v_str_2049_);
lean_dec_ref_known(v_pre_2039_, 2);
v___x_2050_ = lean_string_dec_eq(v_str_2049_, v___x_2029_);
lean_dec_ref(v_str_2049_);
if (v___x_2050_ == 0)
{
lean_dec_ref(v_str_2048_);
lean_dec_ref(v_str_2047_);
lean_dec_ref(v_str_2046_);
lean_del_object(v___x_2044_);
lean_dec_ref(v_args_2042_);
lean_dec(v_info_2041_);
goto v___jp_2005_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_string_dec_eq(v_str_2048_, v___x_2030_);
lean_dec_ref(v_str_2048_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v_str_2047_);
lean_dec_ref(v_str_2046_);
lean_del_object(v___x_2044_);
lean_dec_ref(v_args_2042_);
lean_dec(v_info_2041_);
goto v___jp_2005_;
}
else
{
uint8_t v___x_2052_; 
v___x_2052_ = lean_string_dec_eq(v_str_2047_, v___x_2031_);
lean_dec_ref(v_str_2047_);
if (v___x_2052_ == 0)
{
lean_dec_ref(v_str_2046_);
lean_del_object(v___x_2044_);
lean_dec_ref(v_args_2042_);
lean_dec(v_info_2041_);
goto v___jp_2005_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2054_ = lean_string_dec_eq(v_str_2046_, v___x_2053_);
lean_dec_ref(v_str_2046_);
if (v___x_2054_ == 0)
{
lean_del_object(v___x_2044_);
lean_dec_ref(v_args_2042_);
lean_dec(v_info_2041_);
goto v___jp_2005_;
}
else
{
lean_dec(v_docComment_1852_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_del_object(v___x_2044_);
lean_dec_ref(v_args_2042_);
lean_dec(v_info_2041_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2057_ = l_Lean_Name_str___override(v_pre_2040_, v___x_2029_);
v___x_2058_ = l_Lean_Name_str___override(v___x_2057_, v___x_2030_);
v___x_2059_ = l_Lean_Name_str___override(v___x_2058_, v___x_2031_);
v___x_2060_ = l_Lean_Name_str___override(v___x_2059_, v___x_2053_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 1, v___x_2060_);
v___x_2062_ = v___x_2044_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_info_2041_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_args_2042_);
v___x_2062_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = l_Lean_Syntax_getArg(v___x_2062_, v___x_2063_);
lean_dec_ref(v___x_2062_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
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
lean_dec_ref_known(v_pre_2039_, 2);
lean_dec(v_pre_2040_);
lean_dec_ref_known(v_pre_2038_, 2);
lean_dec_ref_known(v_pre_2037_, 2);
lean_dec_ref_known(v_kind_2036_, 2);
lean_dec_ref_known(v___x_2035_, 3);
goto v___jp_2005_;
}
}
else
{
lean_dec_ref_known(v_pre_2038_, 2);
lean_dec(v_pre_2039_);
lean_dec_ref_known(v_pre_2037_, 2);
lean_dec_ref_known(v_kind_2036_, 2);
lean_dec_ref_known(v___x_2035_, 3);
goto v___jp_2005_;
}
}
else
{
lean_dec(v_pre_2038_);
lean_dec_ref_known(v_pre_2037_, 2);
lean_dec_ref_known(v_kind_2036_, 2);
lean_dec_ref_known(v___x_2035_, 3);
goto v___jp_2005_;
}
}
else
{
lean_dec_ref_known(v_kind_2036_, 2);
lean_dec(v_pre_2037_);
lean_dec_ref_known(v___x_2035_, 3);
goto v___jp_2005_;
}
}
else
{
lean_dec(v_kind_2036_);
lean_dec_ref_known(v___x_2035_, 3);
goto v___jp_2005_;
}
}
else
{
lean_dec(v___x_2035_);
goto v___jp_2005_;
}
}
v___jp_1860_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
v___jp_1863_:
{
lean_object* v___x_1873_; lean_object* v_currNamespace_1874_; lean_object* v_openDecls_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_env_1879_; lean_object* v_nextMacroScope_1880_; lean_object* v_ngen_1881_; lean_object* v_auxDeclNGen_1882_; lean_object* v_traceState_1883_; lean_object* v_cache_1884_; lean_object* v_messages_1885_; lean_object* v_infoState_1886_; lean_object* v_snapshotTasks_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1896_; 
v___x_1873_ = lean_st_ref_take(v___y_1872_);
v_currNamespace_1874_ = lean_ctor_get(v___y_1871_, 6);
v_openDecls_1875_ = lean_ctor_get(v___y_1871_, 7);
lean_inc(v_openDecls_1875_);
lean_inc(v_currNamespace_1874_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_currNamespace_1874_);
lean_ctor_set(v___x_1876_, 1, v_openDecls_1875_);
v___x_1877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___y_1868_);
lean_inc(v___y_1870_);
lean_inc_ref(v___y_1865_);
v___x_1878_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1878_, 0, v___y_1865_);
lean_ctor_set(v___x_1878_, 1, v___y_1866_);
lean_ctor_set(v___x_1878_, 2, v___y_1870_);
lean_ctor_set(v___x_1878_, 3, v___y_1869_);
lean_ctor_set(v___x_1878_, 4, v___x_1877_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*5, v___y_1867_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*5 + 1, v___y_1864_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*5 + 2, v___y_1867_);
v_env_1879_ = lean_ctor_get(v___x_1873_, 0);
v_nextMacroScope_1880_ = lean_ctor_get(v___x_1873_, 1);
v_ngen_1881_ = lean_ctor_get(v___x_1873_, 2);
v_auxDeclNGen_1882_ = lean_ctor_get(v___x_1873_, 3);
v_traceState_1883_ = lean_ctor_get(v___x_1873_, 4);
v_cache_1884_ = lean_ctor_get(v___x_1873_, 5);
v_messages_1885_ = lean_ctor_get(v___x_1873_, 6);
v_infoState_1886_ = lean_ctor_get(v___x_1873_, 7);
v_snapshotTasks_1887_ = lean_ctor_get(v___x_1873_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1889_ = v___x_1873_;
v_isShared_1890_ = v_isSharedCheck_1896_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_snapshotTasks_1887_);
lean_inc(v_infoState_1886_);
lean_inc(v_messages_1885_);
lean_inc(v_cache_1884_);
lean_inc(v_traceState_1883_);
lean_inc(v_auxDeclNGen_1882_);
lean_inc(v_ngen_1881_);
lean_inc(v_nextMacroScope_1880_);
lean_inc(v_env_1879_);
lean_dec(v___x_1873_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1896_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lean_MessageLog_add(v___x_1878_, v_messages_1885_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 6, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_env_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_nextMacroScope_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_ngen_1881_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_auxDeclNGen_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_traceState_1883_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v_cache_1884_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v___x_1891_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v_infoState_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_snapshotTasks_1887_);
v___x_1893_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_st_ref_set(v___y_1872_, v___x_1893_);
goto v___jp_1860_;
}
}
}
v___jp_1897_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; 
lean_inc_ref(v___y_1904_);
v___x_1905_ = l_Lean_Parser_ParserState_allErrors(v___y_1904_);
v___x_1906_ = lean_array_get_size(v___x_1905_);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_nat_dec_eq(v___x_1906_, v___x_1907_);
v___x_1909_ = lean_bool_not(v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v_stxStack_1910_; lean_object* v_pos_1911_; uint8_t v___x_1912_; uint8_t v___x_1913_; 
lean_dec_ref(v___x_1905_);
v_stxStack_1910_ = lean_ctor_get(v___y_1904_, 0);
lean_inc_ref(v_stxStack_1910_);
v_pos_1911_ = lean_ctor_get(v___y_1904_, 2);
lean_inc(v_pos_1911_);
lean_dec_ref(v___y_1904_);
v___x_1912_ = l_Lean_Parser_InputContext_atEnd(v___y_1902_, v_pos_1911_);
lean_dec_ref(v___y_1902_);
v___x_1913_ = lean_bool_not(v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_dec(v_pos_1911_);
v___x_1914_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1910_);
lean_dec_ref(v_stxStack_1910_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint32_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec_ref(v_stxStack_1910_);
lean_inc_ref(v___y_1899_);
v___x_1917_ = l_Lean_FileMap_toPosition(v___y_1899_, v_pos_1911_);
v___x_1918_ = lean_box(0);
v___x_1919_ = 2;
v___x_1920_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__0));
v___x_1921_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__1));
v___x_1922_ = lean_string_utf8_get(v___y_1901_, v_pos_1911_);
lean_dec(v_pos_1911_);
v___x_1923_ = lean_string_push(v___x_1920_, v___x_1922_);
v___x_1924_ = lean_string_append(v___x_1921_, v___x_1923_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__2___closed__2));
v___x_1926_ = lean_string_append(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
v___x_1928_ = l_Lean_MessageData_ofFormat(v___x_1927_);
if (v___y_1903_ == 0)
{
v___y_1864_ = v___x_1919_;
v___y_1865_ = v___y_1900_;
v___y_1866_ = v___x_1917_;
v___y_1867_ = v___x_1909_;
v___y_1868_ = v___x_1928_;
v___y_1869_ = v___x_1920_;
v___y_1870_ = v___x_1918_;
v___y_1871_ = v___y_1857_;
v___y_1872_ = v___y_1858_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; uint8_t v___x_1932_; 
v___x_1929_ = lean_box(v___x_1909_);
v___x_1930_ = lean_box(v___y_1898_);
v___f_1931_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1931_, 0, v___x_1929_);
lean_closure_set(v___f_1931_, 1, v___x_1930_);
lean_inc_ref(v___x_1928_);
v___x_1932_ = l_Lean_MessageData_hasTag(v___f_1931_, v___x_1928_);
if (v___x_1932_ == 0)
{
lean_dec_ref(v___x_1928_);
lean_dec_ref(v___x_1917_);
goto v___jp_1860_;
}
else
{
v___y_1864_ = v___x_1919_;
v___y_1865_ = v___y_1900_;
v___y_1866_ = v___x_1917_;
v___y_1867_ = v___x_1909_;
v___y_1868_ = v___x_1928_;
v___y_1869_ = v___x_1920_;
v___y_1870_ = v___x_1918_;
v___y_1871_ = v___y_1857_;
v___y_1872_ = v___y_1858_;
goto v___jp_1863_;
}
}
}
}
else
{
lean_object* v___x_1933_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1902_);
v___x_1933_ = lean_box(0);
v_sz_1934_ = lean_array_size(v___x_1905_);
v___x_1935_ = ((size_t)0ULL);
lean_inc_ref(v___y_1899_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1899_, v___x_1905_, v_sz_1934_, v___x_1935_, v___x_1933_, v___y_1857_, v___y_1858_);
lean_dec_ref(v___x_1905_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1944_; 
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
lean_object* v_unused_1945_; 
v_unused_1945_ = lean_ctor_get(v___x_1936_, 0);
lean_dec(v_unused_1945_);
v___x_1938_ = v___x_1936_;
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
else
{
lean_dec(v___x_1936_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1944_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_box(0);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1936_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1936_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
v___jp_1954_:
{
if (v___y_1966_ == 0)
{
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1957_);
v___y_1898_ = v___y_1955_;
v___y_1899_ = v___y_1956_;
v___y_1900_ = v___y_1958_;
v___y_1901_ = v___y_1960_;
v___y_1902_ = v___y_1961_;
v___y_1903_ = v___y_1963_;
v___y_1904_ = v___y_1964_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_pos_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___y_1959_);
lean_ctor_set(v___x_1970_, 1, v___x_1967_);
v___x_1971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1967_);
lean_ctor_set(v___x_1971_, 1, v___x_1968_);
lean_ctor_set(v___x_1971_, 2, v___x_1969_);
lean_ctor_set(v___x_1971_, 3, v___x_1970_);
lean_ctor_set(v___x_1971_, 4, v___x_1967_);
v_pos_1972_ = lean_ctor_get(v___y_1964_, 2);
lean_inc(v_pos_1972_);
lean_dec_ref(v___y_1964_);
v___x_1973_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_1973_, 0, v___x_1971_);
v___x_1974_ = l_Lean_Parser_ParserState_setPos(v___y_1957_, v_pos_1972_);
lean_inc_ref(v___y_1961_);
v___x_1975_ = l_Lean_Parser_ParserFn_run(v___x_1973_, v___y_1961_, v___y_1962_, v___y_1965_, v___x_1974_);
v___y_1898_ = v___y_1955_;
v___y_1899_ = v___y_1956_;
v___y_1900_ = v___y_1958_;
v___y_1901_ = v___y_1960_;
v___y_1902_ = v___y_1961_;
v___y_1903_ = v___y_1963_;
v___y_1904_ = v___x_1975_;
goto v___jp_1897_;
}
}
v___jp_1976_:
{
lean_object* v___x_1988_; lean_object* v_env_1989_; lean_object* v_ictx_1990_; lean_object* v_pmctx_1991_; lean_object* v_blockCtxt_1992_; lean_object* v___x_1993_; lean_object* v_s_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_s_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1988_ = lean_st_ref_get(v___y_1858_);
v_env_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref_n(v_env_1989_, 2);
lean_dec(v___x_1988_);
lean_inc(v___y_1987_);
lean_inc_ref_n(v___y_1979_, 2);
lean_inc_ref(v___y_1981_);
lean_inc_ref(v___y_1977_);
v_ictx_1990_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_1990_, 0, v___y_1977_);
lean_ctor_set(v_ictx_1990_, 1, v___y_1981_);
lean_ctor_set(v_ictx_1990_, 2, v___y_1979_);
lean_ctor_set(v_ictx_1990_, 3, v___y_1987_);
lean_inc(v___y_1985_);
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1983_);
v_pmctx_1991_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_1991_, 0, v_env_1989_);
lean_ctor_set(v_pmctx_1991_, 1, v___y_1983_);
lean_ctor_set(v_pmctx_1991_, 2, v___y_1980_);
lean_ctor_set(v_pmctx_1991_, 3, v___y_1985_);
lean_inc(v___y_1986_);
v_blockCtxt_1992_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1979_, v___y_1986_, v___y_1987_);
v___x_1993_ = l_Lean_Parser_mkParserState(v___y_1977_);
lean_inc_ref(v___x_1993_);
v_s_1994_ = l_Lean_Parser_ParserState_setPos(v___x_1993_, v___y_1986_);
v___x_1995_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_1995_, 0, v_blockCtxt_1992_);
v___x_1996_ = l_Lean_Parser_getTokenTable(v_env_1989_);
lean_inc_ref(v___x_1996_);
lean_inc_ref(v_pmctx_1991_);
lean_inc_ref(v_ictx_1990_);
v_s_1997_ = l_Lean_Parser_ParserFn_run(v___x_1995_, v_ictx_1990_, v_pmctx_1991_, v___x_1996_, v_s_1994_);
lean_inc_ref(v_s_1997_);
v___x_1998_ = l_Lean_Parser_ParserState_allErrors(v_s_1997_);
v___x_1999_ = lean_array_get_size(v___x_1998_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = lean_unsigned_to_nat(0u);
v___x_2001_ = lean_nat_dec_eq(v___x_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
v___y_1955_ = v___y_1978_;
v___y_1956_ = v___y_1979_;
v___y_1957_ = v___x_1993_;
v___y_1958_ = v___y_1981_;
v___y_1959_ = v___y_1982_;
v___y_1960_ = v___y_1977_;
v___y_1961_ = v_ictx_1990_;
v___y_1962_ = v_pmctx_1991_;
v___y_1963_ = v___y_1984_;
v___y_1964_ = v_s_1997_;
v___y_1965_ = v___x_1996_;
v___y_1966_ = v___x_2001_;
goto v___jp_1954_;
}
else
{
lean_object* v_pos_2002_; uint8_t v___x_2003_; uint8_t v___x_2004_; 
v_pos_2002_ = lean_ctor_get(v_s_1997_, 2);
lean_inc(v_pos_2002_);
v___x_2003_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1990_, v_pos_2002_);
lean_dec(v_pos_2002_);
v___x_2004_ = lean_bool_not(v___x_2003_);
v___y_1955_ = v___y_1978_;
v___y_1956_ = v___y_1979_;
v___y_1957_ = v___x_1993_;
v___y_1958_ = v___y_1981_;
v___y_1959_ = v___y_1982_;
v___y_1960_ = v___y_1977_;
v___y_1961_ = v_ictx_1990_;
v___y_1962_ = v_pmctx_1991_;
v___y_1963_ = v___y_1984_;
v___y_1964_ = v_s_1997_;
v___y_1965_ = v___x_1996_;
v___y_1966_ = v___x_2004_;
goto v___jp_1954_;
}
}
v___jp_2005_:
{
lean_object* v_fileName_2006_; lean_object* v_fileMap_2007_; lean_object* v_options_2008_; lean_object* v_currNamespace_2009_; lean_object* v_openDecls_2010_; uint8_t v_suppressElabErrors_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v_fileName_2006_ = lean_ctor_get(v___y_1857_, 0);
v_fileMap_2007_ = lean_ctor_get(v___y_1857_, 1);
v_options_2008_ = lean_ctor_get(v___y_1857_, 2);
v_currNamespace_2009_ = lean_ctor_get(v___y_1857_, 6);
v_openDecls_2010_ = lean_ctor_get(v___y_1857_, 7);
v_suppressElabErrors_2011_ = lean_ctor_get_uint8(v___y_1857_, sizeof(void*)*14 + 1);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = l_Lean_Syntax_getArg(v_docComment_1852_, v___x_2012_);
v___x_2014_ = 1;
v___x_2015_ = l_Lean_Syntax_getPos_x3f(v___x_2013_, v___x_2014_);
if (lean_obj_tag(v___x_2015_) == 1)
{
lean_object* v_val_2016_; lean_object* v___x_2017_; 
v_val_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Lean_Syntax_getTailPos_x3f(v___x_2013_, v___x_2014_);
lean_dec(v___x_2013_);
if (lean_obj_tag(v___x_2017_) == 1)
{
lean_object* v_val_2018_; lean_object* v_source_2019_; lean_object* v___x_2020_; lean_object* v_endPos_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
lean_dec(v_docComment_1852_);
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v_source_2019_ = lean_ctor_get(v_fileMap_2007_, 0);
v___x_2020_ = lean_string_utf8_prev(v_source_2019_, v_val_2018_);
lean_dec(v_val_2018_);
v_endPos_2021_ = lean_string_utf8_prev(v_source_2019_, v___x_2020_);
lean_dec(v___x_2020_);
v___x_2022_ = lean_string_utf8_byte_size(v_source_2019_);
v___x_2023_ = lean_nat_dec_le(v_endPos_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
lean_dec(v_endPos_2021_);
v___y_1977_ = v_source_2019_;
v___y_1978_ = v_suppressElabErrors_2011_;
v___y_1979_ = v_fileMap_2007_;
v___y_1980_ = v_currNamespace_2009_;
v___y_1981_ = v_fileName_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v_options_2008_;
v___y_1984_ = v_suppressElabErrors_2011_;
v___y_1985_ = v_openDecls_2010_;
v___y_1986_ = v_val_2016_;
v___y_1987_ = v___x_2022_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v_source_2019_;
v___y_1978_ = v_suppressElabErrors_2011_;
v___y_1979_ = v_fileMap_2007_;
v___y_1980_ = v_currNamespace_2009_;
v___y_1981_ = v_fileName_2006_;
v___y_1982_ = v___x_2012_;
v___y_1983_ = v_options_2008_;
v___y_1984_ = v_suppressElabErrors_2011_;
v___y_1985_ = v_openDecls_2010_;
v___y_1986_ = v_val_2016_;
v___y_1987_ = v_endPos_2021_;
goto v___jp_1976_;
}
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v___x_2017_);
lean_dec(v_val_2016_);
v___x_2024_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2025_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1852_, v___x_2024_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v_docComment_1852_);
return v___x_2025_;
}
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v___x_2015_);
lean_dec(v___x_2013_);
v___x_2026_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2027_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1852_, v___x_2026_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v_docComment_1852_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2092_, lean_object* v_binders_2093_, lean_object* v_docComment_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v_body_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_unsigned_to_nat(1u);
v_body_2103_ = l_Lean_Syntax_getArg(v_docComment_2094_, v___x_2102_);
v___x_2104_ = 1;
v___x_2105_ = l_Lean_Syntax_getPos_x3f(v_body_2103_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2103_);
v___x_2107_ = l_Lean_Syntax_isOfKind(v_body_2103_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_dec(v_body_2103_);
v___x_2108_ = l_Lean_TSyntax_getDocString(v_docComment_2094_);
lean_dec(v_docComment_2094_);
v___x_2109_ = l_Lean_versoDocStringOfText(v_declName_2092_, v_binders_2093_, v___x_2108_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
lean_dec(v_docComment_2094_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = l_Lean_Syntax_getArg(v_body_2103_, v___x_2110_);
lean_dec(v_body_2103_);
v___x_2112_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2111_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = l_Lean_Syntax_getArgs(v___x_2111_);
lean_dec(v___x_2111_);
v___x_2115_ = lean_box(0);
v___x_2116_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2092_, v_binders_2093_, v___x_2114_, v___x_2115_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = l_Lean_Syntax_getArg(v___x_2111_, v___x_2110_);
lean_dec(v___x_2111_);
v___x_2118_ = l_Lean_Syntax_getAtomVal(v___x_2117_);
lean_dec(v___x_2117_);
v___x_2119_ = l_Lean_versoDocStringOfText(v_declName_2092_, v_binders_2093_, v___x_2118_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v___x_2119_;
}
}
}
else
{
lean_object* v___x_2120_; 
lean_dec_ref_known(v___x_2105_, 1);
lean_dec(v_body_2103_);
v___x_2120_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2171_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2171_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2171_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
if (lean_obj_tag(v_a_2121_) == 1)
{
lean_object* v_val_2125_; lean_object* v___x_2126_; size_t v_sz_2127_; size_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
lean_del_object(v___x_2123_);
v_val_2125_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_a_2121_, 1);
v___x_2126_ = l_Lean_Syntax_getArgs(v_val_2125_);
lean_dec(v_val_2125_);
v_sz_2127_ = lean_array_size(v___x_2126_);
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2127_, v___x_2128_, v___x_2126_);
v___x_2130_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2092_, v_binders_2093_, v___x_2130_, v___x_2131_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2158_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2158_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2158_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v_fst_2137_; lean_object* v_snd_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2157_; 
v_fst_2137_ = lean_ctor_get(v_a_2133_, 0);
v_snd_2138_ = lean_ctor_get(v_a_2133_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2140_ = v_a_2133_;
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_snd_2138_);
lean_inc(v_fst_2137_);
lean_dec(v_a_2133_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2156_; 
v_fst_2142_ = lean_ctor_get(v_fst_2137_, 0);
v_snd_2143_ = lean_ctor_get(v_fst_2137_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_fst_2137_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2145_ = v_fst_2137_;
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snd_2143_);
lean_inc(v_fst_2142_);
lean_dec(v_fst_2137_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_fst_2142_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_snd_2143_);
v___x_2148_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2148_);
v___x_2150_ = v___x_2140_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2138_);
v___x_2150_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2150_);
v___x_2152_ = v___x_2135_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
v_a_2159_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2132_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2132_);
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
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec(v_a_2121_);
lean_dec(v_binders_2093_);
lean_dec(v_declName_2092_);
v___x_2167_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2167_);
v___x_2169_ = v___x_2123_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_binders_2093_);
lean_dec(v_declName_2092_);
v_a_2172_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2120_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2120_);
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
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2180_, lean_object* v_binders_2181_, lean_object* v_docComment_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_versoDocString(v_declName_2180_, v_binders_2181_, v_docComment_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2191_, lean_object* v_as_2192_, size_t v_sz_2193_, size_t v_i_2194_, lean_object* v_b_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2191_, v_as_2192_, v_sz_2193_, v_i_2194_, v_b_2195_, v___y_2200_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2204_, lean_object* v_as_2205_, lean_object* v_sz_2206_, lean_object* v_i_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
size_t v_sz_boxed_2216_; size_t v_i_boxed_2217_; lean_object* v_res_2218_; 
v_sz_boxed_2216_ = lean_unbox_usize(v_sz_2206_);
lean_dec(v_sz_2206_);
v_i_boxed_2217_ = lean_unbox_usize(v_i_2207_);
lean_dec(v_i_2207_);
v_res_2218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2204_, v_as_2205_, v_sz_boxed_2216_, v_i_boxed_2217_, v_b_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_as_2205_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2219_, lean_object* v_ref_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2220_, v_msg_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2230_, lean_object* v_ref_2231_, lean_object* v_msg_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2230_, v_ref_2231_, v_msg_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v_ref_2231_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2241_, lean_object* v_msg_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2251_, v_msg_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2261_, lean_object* v_macroStack_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2261_, v_macroStack_2262_, v___y_2267_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2271_, lean_object* v_macroStack_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2271_, v_macroStack_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2281_, lean_object* v_doc_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v___x_2290_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2298_; lean_object* v_env_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2290_ = lean_st_ref_get(v_a_2288_);
v_env_2305_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_ref(v_env_2305_);
lean_dec(v___x_2290_);
v___x_2306_ = l_Lean_getMainVersoModuleDocs(v_env_2305_);
v___x_2307_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2306_);
lean_dec_ref(v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
v___y_2298_ = v___x_2307_;
goto v___jp_2297_;
}
else
{
lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2317_; 
v_val_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2317_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2317_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_add(v_val_2308_, v___x_2312_);
lean_dec(v_val_2308_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2313_);
v___x_2315_ = v___x_2310_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
v___y_2298_ = v___x_2315_;
goto v___jp_2297_;
}
}
}
v___jp_2291_:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2294_, 0, v_range_2281_);
lean_closure_set(v___x_2294_, 1, v___y_2292_);
lean_closure_set(v___x_2294_, 2, v___y_2293_);
v___x_2295_ = 0;
v___x_2296_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2294_, v___x_2295_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2296_;
}
v___jp_2297_:
{
lean_object* v___x_2299_; size_t v_sz_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = l_Lean_Syntax_getArgs(v_doc_2282_);
v_sz_2300_ = lean_array_size(v___x_2299_);
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2300_, v___x_2301_, v___x_2299_);
if (lean_obj_tag(v___y_2298_) == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_unsigned_to_nat(0u);
v___y_2292_ = v___x_2302_;
v___y_2293_ = v___x_2303_;
goto v___jp_2291_;
}
else
{
lean_object* v_val_2304_; 
v_val_2304_ = lean_ctor_get(v___y_2298_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___y_2298_, 1);
v___y_2292_ = v___x_2302_;
v___y_2293_ = v_val_2304_;
goto v___jp_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2318_, lean_object* v_doc_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_versoModDocString(v_range_2318_, v_doc_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec(v_a_2325_);
lean_dec_ref(v_a_2324_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_doc_2319_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2337_, lean_object* v_docComment_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2347_ = l_Lean_versoDocStringOfText(v_declName_2337_, v___x_2346_, v_docComment_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2348_, lean_object* v_docComment_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_versoDocStringFromString(v_declName_2348_, v_docComment_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2358_, lean_object* v_declName_2359_, lean_object* v_env_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = l_Lean_docStringExt;
v___x_2362_ = l_String_removeLeadingSpaces(v_docString_2358_);
v___x_2363_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2361_, v_env_2360_, v_declName_2359_, v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2364_, lean_object* v_modifyEnv_2365_, lean_object* v_docString_2366_){
_start:
{
lean_object* v___f_2367_; lean_object* v___x_2368_; 
v___f_2367_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2367_, 0, v_docString_2366_);
lean_closure_set(v___f_2367_, 1, v_declName_2364_);
v___x_2368_ = lean_apply_1(v_modifyEnv_2365_, v___f_2367_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_docComment_2371_, lean_object* v_toBind_2372_, lean_object* v___f_2373_, lean_object* v_____r_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = l_Lean_getDocStringText___redArg(v_inst_2369_, v_inst_2370_, v_docComment_2371_);
v___x_2376_ = lean_apply_4(v_toBind_2372_, lean_box(0), lean_box(0), v___x_2375_, v___f_2373_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_docComment_2382_, lean_object* v_toBind_2383_, lean_object* v___f_2384_, lean_object* v_____r_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = l_Lean_validateDocComment___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_docComment_2382_);
v___x_2387_ = lean_apply_4(v_toBind_2383_, lean_box(0), lean_box(0), v___x_2386_, v___f_2384_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_inst_2392_, lean_object* v_docComment_2393_, lean_object* v_toBind_2394_, lean_object* v___f_2395_, lean_object* v_____r_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2388_, v_inst_2389_, v_inst_2390_, v_inst_2391_, v_inst_2392_, v_docComment_2393_, v_toBind_2394_, v___f_2395_, v_____r_2396_);
lean_dec(v_docComment_2393_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2398_, lean_object* v_____r_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_apply_1(v___f_2398_, v_____r_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2403_ = l_Lean_stringToMessageData(v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2406_ = l_Lean_stringToMessageData(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2407_, lean_object* v_declName_2408_, uint8_t v___x_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_toBind_2412_, lean_object* v___f_2413_, lean_object* v_____do__lift_2414_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2414_, v_declName_2408_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_dec(v___f_2413_);
lean_dec(v_toBind_2412_);
lean_dec_ref(v_inst_2411_);
lean_dec_ref(v_inst_2410_);
lean_dec(v_declName_2408_);
goto v___jp_2415_;
}
else
{
lean_dec_ref_known(v___x_2418_, 1);
if (v___x_2409_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec(v___f_2407_);
v___x_2419_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2420_ = l_Lean_MessageData_ofConstName(v_declName_2408_, v___x_2409_);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_throwError___redArg(v_inst_2410_, v_inst_2411_, v___x_2423_);
v___x_2425_ = lean_apply_4(v_toBind_2412_, lean_box(0), lean_box(0), v___x_2424_, v___f_2413_);
return v___x_2425_;
}
else
{
lean_dec(v___f_2413_);
lean_dec(v_toBind_2412_);
lean_dec_ref(v_inst_2411_);
lean_dec_ref(v_inst_2410_);
lean_dec(v_declName_2408_);
goto v___jp_2415_;
}
}
v___jp_2415_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_box(0);
v___x_2417_ = lean_apply_1(v___f_2407_, v___x_2416_);
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2426_, lean_object* v_declName_2427_, lean_object* v___x_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_toBind_2431_, lean_object* v___f_2432_, lean_object* v_____do__lift_2433_){
_start:
{
uint8_t v___x_390__boxed_2434_; lean_object* v_res_2435_; 
v___x_390__boxed_2434_ = lean_unbox(v___x_2428_);
v_res_2435_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2426_, v_declName_2427_, v___x_390__boxed_2434_, v_inst_2429_, v_inst_2430_, v_toBind_2431_, v___f_2432_, v_____do__lift_2433_);
lean_dec_ref(v_____do__lift_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_declName_2443_, lean_object* v_docComment_2444_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = l_Lean_Name_isAnonymous(v_declName_2443_);
if (v___x_2445_ == 0)
{
lean_object* v_toBind_2446_; lean_object* v_getEnv_2447_; lean_object* v_modifyEnv_2448_; lean_object* v___f_2449_; lean_object* v___f_2450_; lean_object* v___f_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___f_2454_; lean_object* v___x_2455_; 
v_toBind_2446_ = lean_ctor_get(v_inst_2436_, 1);
lean_inc_n(v_toBind_2446_, 4);
v_getEnv_2447_ = lean_ctor_get(v_inst_2439_, 0);
lean_inc(v_getEnv_2447_);
v_modifyEnv_2448_ = lean_ctor_get(v_inst_2439_, 1);
lean_inc(v_modifyEnv_2448_);
lean_dec_ref(v_inst_2439_);
lean_inc(v_declName_2443_);
v___f_2449_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2449_, 0, v_declName_2443_);
lean_closure_set(v___f_2449_, 1, v_modifyEnv_2448_);
lean_inc(v_docComment_2444_);
lean_inc_ref(v_inst_2440_);
lean_inc_ref_n(v_inst_2436_, 2);
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2450_, 0, v_inst_2436_);
lean_closure_set(v___f_2450_, 1, v_inst_2440_);
lean_closure_set(v___f_2450_, 2, v_docComment_2444_);
lean_closure_set(v___f_2450_, 3, v_toBind_2446_);
lean_closure_set(v___f_2450_, 4, v___f_2449_);
v___f_2451_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2451_, 0, v_inst_2436_);
lean_closure_set(v___f_2451_, 1, v_inst_2437_);
lean_closure_set(v___f_2451_, 2, v_inst_2441_);
lean_closure_set(v___f_2451_, 3, v_inst_2442_);
lean_closure_set(v___f_2451_, 4, v_inst_2438_);
lean_closure_set(v___f_2451_, 5, v_docComment_2444_);
lean_closure_set(v___f_2451_, 6, v_toBind_2446_);
lean_closure_set(v___f_2451_, 7, v___f_2450_);
lean_inc_ref(v___f_2451_);
v___f_2452_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2452_, 0, v___f_2451_);
v___x_2453_ = lean_box(v___x_2445_);
v___f_2454_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2454_, 0, v___f_2451_);
lean_closure_set(v___f_2454_, 1, v_declName_2443_);
lean_closure_set(v___f_2454_, 2, v___x_2453_);
lean_closure_set(v___f_2454_, 3, v_inst_2436_);
lean_closure_set(v___f_2454_, 4, v_inst_2440_);
lean_closure_set(v___f_2454_, 5, v_toBind_2446_);
lean_closure_set(v___f_2454_, 6, v___f_2452_);
v___x_2455_ = lean_apply_4(v_toBind_2446_, lean_box(0), lean_box(0), v_getEnv_2447_, v___f_2454_);
return v___x_2455_;
}
else
{
lean_object* v_toApplicative_2456_; lean_object* v_toPure_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
lean_dec(v_docComment_2444_);
lean_dec(v_declName_2443_);
lean_dec(v_inst_2442_);
lean_dec_ref(v_inst_2441_);
lean_dec_ref(v_inst_2440_);
lean_dec_ref(v_inst_2439_);
lean_dec(v_inst_2438_);
lean_dec(v_inst_2437_);
v_toApplicative_2456_ = lean_ctor_get(v_inst_2436_, 0);
lean_inc_ref(v_toApplicative_2456_);
lean_dec_ref(v_inst_2436_);
v_toPure_2457_ = lean_ctor_get(v_toApplicative_2456_, 1);
lean_inc(v_toPure_2457_);
lean_dec_ref(v_toApplicative_2456_);
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_apply_2(v_toPure_2457_, lean_box(0), v___x_2458_);
return v___x_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_declName_2468_, lean_object* v_docComment_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_addMarkdownDocString___redArg(v_inst_2461_, v_inst_2462_, v_inst_2463_, v_inst_2464_, v_inst_2465_, v_inst_2466_, v_inst_2467_, v_declName_2468_, v_docComment_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2471_, lean_object* v_x1_2472_, lean_object* v_x2_2473_){
_start:
{
lean_object* v_index_2474_; lean_object* v_sourceString_2475_; lean_object* v_imports_2476_; lean_object* v_currNamespace_2477_; lean_object* v_openDecls_2478_; lean_object* v_options_2479_; lean_object* v_check_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2493_; 
v_index_2474_ = lean_ctor_get(v_x2_2473_, 1);
v_sourceString_2475_ = lean_ctor_get(v_x2_2473_, 2);
v_imports_2476_ = lean_ctor_get(v_x2_2473_, 3);
v_currNamespace_2477_ = lean_ctor_get(v_x2_2473_, 4);
v_openDecls_2478_ = lean_ctor_get(v_x2_2473_, 5);
v_options_2479_ = lean_ctor_get(v_x2_2473_, 6);
v_check_2480_ = lean_ctor_get(v_x2_2473_, 7);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_x2_2473_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_x2_2473_, 0);
lean_dec(v_unused_2494_);
v___x_2482_ = v_x2_2473_;
v_isShared_2483_ = v_isSharedCheck_2493_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_check_2480_);
lean_inc(v_options_2479_);
lean_inc(v_openDecls_2478_);
lean_inc(v_currNamespace_2477_);
lean_inc(v_imports_2476_);
lean_inc(v_sourceString_2475_);
lean_inc(v_index_2474_);
lean_dec(v_x2_2473_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2493_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v_toEnvExtension_2485_; lean_object* v_asyncMode_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2484_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2485_ = lean_ctor_get(v___x_2484_, 0);
v_asyncMode_2486_ = lean_ctor_get(v_toEnvExtension_2485_, 2);
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_declName_2471_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2487_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_index_2474_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_sourceString_2475_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_imports_2476_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_currNamespace_2477_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v_openDecls_2478_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_options_2479_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_check_2480_);
v___x_2489_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_box(0);
v___x_2491_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2484_, v_x1_2472_, v___x_2489_, v_asyncMode_2486_, v___x_2490_);
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2514_, lean_object* v_docs_2515_, lean_object* v_deferred_2516_, lean_object* v___f_2517_, lean_object* v_env_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v_env_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2519_ = l_Lean_versoDocStringExt;
v_env_2520_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2519_, v_env_2518_, v_declName_2514_, v_docs_2515_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_array_get_size(v_deferred_2516_);
v___x_2523_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2524_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v___f_2517_);
lean_dec_ref(v_deferred_2516_);
return v_env_2520_;
}
else
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_nat_dec_le(v___x_2522_, v___x_2522_);
if (v___x_2525_ == 0)
{
if (v___x_2524_ == 0)
{
lean_dec_ref(v___f_2517_);
lean_dec_ref(v_deferred_2516_);
return v_env_2520_;
}
else
{
size_t v___x_2526_; size_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = ((size_t)0ULL);
v___x_2527_ = lean_usize_of_nat(v___x_2522_);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2523_, v___f_2517_, v_deferred_2516_, v___x_2526_, v___x_2527_, v_env_2520_);
return v___x_2528_;
}
}
else
{
size_t v___x_2529_; size_t v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((size_t)0ULL);
v___x_2530_ = lean_usize_of_nat(v___x_2522_);
v___x_2531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2523_, v___f_2517_, v_deferred_2516_, v___x_2529_, v___x_2530_, v_env_2520_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2532_, lean_object* v___f_2533_, lean_object* v_____r_2534_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_apply_1(v_modifyEnv_2532_, v___f_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2538_, lean_object* v_modifyEnv_2539_, lean_object* v___f_2540_, uint8_t v___x_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_toBind_2544_, lean_object* v___f_2545_, lean_object* v_____do__lift_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2546_, v_declName_2538_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; 
lean_dec(v___f_2545_);
lean_dec(v_toBind_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec(v_declName_2538_);
v___x_2548_ = lean_apply_1(v_modifyEnv_2539_, v___f_2540_);
return v___x_2548_;
}
else
{
lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2547_, 0);
lean_dec(v_unused_2566_);
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2565_;
goto v_resetjp_2549_;
}
else
{
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2565_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (v___x_2541_ == 0)
{
lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
lean_dec_ref(v___f_2540_);
lean_dec(v_modifyEnv_2539_);
v___x_2552_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2553_ = 1;
v___x_2554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2538_, v___x_2553_);
v___x_2555_ = lean_string_append(v___x_2552_, v___x_2554_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2557_ = lean_string_append(v___x_2555_, v___x_2556_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set_tag(v___x_2550_, 3);
lean_ctor_set(v___x_2550_, 0, v___x_2557_);
v___x_2559_ = v___x_2550_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = l_Lean_MessageData_ofFormat(v___x_2559_);
v___x_2561_ = l_Lean_throwError___redArg(v_inst_2542_, v_inst_2543_, v___x_2560_);
v___x_2562_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2561_, v___f_2545_);
return v___x_2562_;
}
}
else
{
lean_object* v___x_2564_; 
lean_del_object(v___x_2550_);
lean_dec(v___f_2545_);
lean_dec(v_toBind_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec(v_declName_2538_);
v___x_2564_ = lean_apply_1(v_modifyEnv_2539_, v___f_2540_);
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2567_, lean_object* v_modifyEnv_2568_, lean_object* v___f_2569_, lean_object* v___x_2570_, lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_toBind_2573_, lean_object* v___f_2574_, lean_object* v_____do__lift_2575_){
_start:
{
uint8_t v___x_577__boxed_2576_; lean_object* v_res_2577_; 
v___x_577__boxed_2576_ = lean_unbox(v___x_2570_);
v_res_2577_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2567_, v_modifyEnv_2568_, v___f_2569_, v___x_577__boxed_2576_, v_inst_2571_, v_inst_2572_, v_toBind_2573_, v___f_2574_, v_____do__lift_2575_);
lean_dec_ref(v_____do__lift_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_declName_2581_, lean_object* v_docs_2582_, lean_object* v_deferred_2583_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = l_Lean_Name_isAnonymous(v_declName_2581_);
if (v___x_2584_ == 0)
{
lean_object* v_toBind_2585_; lean_object* v_getEnv_2586_; lean_object* v_modifyEnv_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; 
v_toBind_2585_ = lean_ctor_get(v_inst_2578_, 1);
lean_inc_n(v_toBind_2585_, 2);
v_getEnv_2586_ = lean_ctor_get(v_inst_2579_, 0);
lean_inc(v_getEnv_2586_);
v_modifyEnv_2587_ = lean_ctor_get(v_inst_2579_, 1);
lean_inc_n(v_modifyEnv_2587_, 2);
lean_dec_ref(v_inst_2579_);
lean_inc_n(v_declName_2581_, 2);
v___f_2588_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2588_, 0, v_declName_2581_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2589_, 0, v_declName_2581_);
lean_closure_set(v___f_2589_, 1, v_docs_2582_);
lean_closure_set(v___f_2589_, 2, v_deferred_2583_);
lean_closure_set(v___f_2589_, 3, v___f_2588_);
lean_inc_ref(v___f_2589_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2590_, 0, v_modifyEnv_2587_);
lean_closure_set(v___f_2590_, 1, v___f_2589_);
v___x_2591_ = lean_box(v___x_2584_);
v___f_2592_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2592_, 0, v_declName_2581_);
lean_closure_set(v___f_2592_, 1, v_modifyEnv_2587_);
lean_closure_set(v___f_2592_, 2, v___f_2589_);
lean_closure_set(v___f_2592_, 3, v___x_2591_);
lean_closure_set(v___f_2592_, 4, v_inst_2578_);
lean_closure_set(v___f_2592_, 5, v_inst_2580_);
lean_closure_set(v___f_2592_, 6, v_toBind_2585_);
lean_closure_set(v___f_2592_, 7, v___f_2590_);
v___x_2593_ = lean_apply_4(v_toBind_2585_, lean_box(0), lean_box(0), v_getEnv_2586_, v___f_2592_);
return v___x_2593_;
}
else
{
lean_object* v_toApplicative_2594_; lean_object* v_toPure_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec_ref(v_deferred_2583_);
lean_dec_ref(v_docs_2582_);
lean_dec(v_declName_2581_);
lean_dec_ref(v_inst_2580_);
lean_dec_ref(v_inst_2579_);
v_toApplicative_2594_ = lean_ctor_get(v_inst_2578_, 0);
lean_inc_ref(v_toApplicative_2594_);
lean_dec_ref(v_inst_2578_);
v_toPure_2595_ = lean_ctor_get(v_toApplicative_2594_, 1);
lean_inc(v_toPure_2595_);
lean_dec_ref(v_toApplicative_2594_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_apply_2(v_toPure_2595_, lean_box(0), v___x_2596_);
return v___x_2597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2598_, lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_declName_2603_, lean_object* v_docs_2604_, lean_object* v_deferred_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2599_, v_inst_2600_, v_inst_2602_, v_declName_2603_, v_docs_2604_, v_deferred_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_declName_2612_, lean_object* v_docs_2613_, lean_object* v_deferred_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_addVersoDocStringCore(v_m_2607_, v_inst_2608_, v_inst_2609_, v_inst_2610_, v_inst_2611_, v_declName_2612_, v_docs_2613_, v_deferred_2614_);
lean_dec(v_inst_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2616_, lean_object* v_x1_2617_, lean_object* v_x2_2618_){
_start:
{
lean_object* v_index_2619_; lean_object* v_sourceString_2620_; lean_object* v_imports_2621_; lean_object* v_currNamespace_2622_; lean_object* v_openDecls_2623_; lean_object* v_options_2624_; lean_object* v_check_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2638_; 
v_index_2619_ = lean_ctor_get(v_x2_2618_, 1);
v_sourceString_2620_ = lean_ctor_get(v_x2_2618_, 2);
v_imports_2621_ = lean_ctor_get(v_x2_2618_, 3);
v_currNamespace_2622_ = lean_ctor_get(v_x2_2618_, 4);
v_openDecls_2623_ = lean_ctor_get(v_x2_2618_, 5);
v_options_2624_ = lean_ctor_get(v_x2_2618_, 6);
v_check_2625_ = lean_ctor_get(v_x2_2618_, 7);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_x2_2618_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; 
v_unused_2639_ = lean_ctor_get(v_x2_2618_, 0);
lean_dec(v_unused_2639_);
v___x_2627_ = v_x2_2618_;
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_check_2625_);
lean_inc(v_options_2624_);
lean_inc(v_openDecls_2623_);
lean_inc(v_currNamespace_2622_);
lean_inc(v_imports_2621_);
lean_inc(v_sourceString_2620_);
lean_inc(v_index_2619_);
lean_dec(v_x2_2618_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2638_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2629_; lean_object* v_toEnvExtension_2630_; lean_object* v_asyncMode_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2629_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2630_ = lean_ctor_get(v___x_2629_, 0);
v_asyncMode_2631_ = lean_ctor_get(v_toEnvExtension_2630_, 2);
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_size_2616_);
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v___x_2632_);
v___x_2634_ = v___x_2627_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_index_2619_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v_sourceString_2620_);
lean_ctor_set(v_reuseFailAlloc_2637_, 3, v_imports_2621_);
lean_ctor_set(v_reuseFailAlloc_2637_, 4, v_currNamespace_2622_);
lean_ctor_set(v_reuseFailAlloc_2637_, 5, v_openDecls_2623_);
lean_ctor_set(v_reuseFailAlloc_2637_, 6, v_options_2624_);
lean_ctor_set(v_reuseFailAlloc_2637_, 7, v_check_2625_);
v___x_2634_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_box(0);
v___x_2636_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2629_, v_x1_2617_, v___x_2634_, v_asyncMode_2631_, v___x_2635_);
return v___x_2636_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2643_, lean_object* v_inst_2644_, lean_object* v_inst_2645_, lean_object* v_deferred_2646_, lean_object* v_inst_2647_, lean_object* v___f_2648_, lean_object* v_____do__lift_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2649_, v_docs_2643_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v___f_2648_);
lean_dec_ref(v_inst_2647_);
lean_dec_ref(v_deferred_2646_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2653_ = l_Lean_stringToMessageData(v_a_2651_);
v___x_2654_ = l_Lean_indentD(v___x_2653_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_throwError___redArg(v_inst_2644_, v_inst_2645_, v___x_2655_);
return v___x_2656_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_dec_ref(v_inst_2645_);
lean_dec_ref(v_inst_2644_);
v_a_2657_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = lean_array_get_size(v_deferred_2646_);
v___x_2660_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2661_ = lean_nat_dec_lt(v___x_2658_, v___x_2659_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v___f_2648_);
lean_dec_ref(v_deferred_2646_);
v___x_2662_ = l_Lean_setEnv___redArg(v_inst_2647_, v_a_2657_);
return v___x_2662_;
}
else
{
uint8_t v___x_2663_; 
v___x_2663_ = lean_nat_dec_le(v___x_2659_, v___x_2659_);
if (v___x_2663_ == 0)
{
if (v___x_2661_ == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref(v___f_2648_);
lean_dec_ref(v_deferred_2646_);
v___x_2664_ = l_Lean_setEnv___redArg(v_inst_2647_, v_a_2657_);
return v___x_2664_;
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_of_nat(v___x_2659_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2660_, v___f_2648_, v_deferred_2646_, v___x_2665_, v___x_2666_, v_a_2657_);
v___x_2668_ = l_Lean_setEnv___redArg(v_inst_2647_, v___x_2667_);
return v___x_2668_;
}
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2669_ = ((size_t)0ULL);
v___x_2670_ = lean_usize_of_nat(v___x_2659_);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2660_, v___f_2648_, v_deferred_2646_, v___x_2669_, v___x_2670_, v_a_2657_);
v___x_2672_ = l_Lean_setEnv___redArg(v_inst_2647_, v___x_2671_);
return v___x_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_deferred_2676_, lean_object* v_inst_2677_, lean_object* v_toBind_2678_, lean_object* v_getEnv_2679_, lean_object* v_____do__lift_2680_){
_start:
{
lean_object* v___x_2681_; lean_object* v_size_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; 
v___x_2681_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2680_);
v_size_2682_ = lean_ctor_get(v___x_2681_, 2);
lean_inc(v_size_2682_);
lean_dec_ref(v___x_2681_);
v___f_2683_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2683_, 0, v_size_2682_);
v___f_2684_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2684_, 0, v_docs_2673_);
lean_closure_set(v___f_2684_, 1, v_inst_2674_);
lean_closure_set(v___f_2684_, 2, v_inst_2675_);
lean_closure_set(v___f_2684_, 3, v_deferred_2676_);
lean_closure_set(v___f_2684_, 4, v_inst_2677_);
lean_closure_set(v___f_2684_, 5, v___f_2683_);
v___x_2685_ = lean_apply_4(v_toBind_2678_, lean_box(0), lean_box(0), v_getEnv_2679_, v___f_2684_);
return v___x_2685_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2688_ = l_Lean_stringToMessageData(v___x_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_toBind_2691_, lean_object* v_getEnv_2692_, lean_object* v___f_2693_, lean_object* v_____do__lift_2694_){
_start:
{
lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = l_Lean_getMainModuleDoc(v_____do__lift_2694_);
v___x_2696_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2695_);
lean_dec_ref(v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec(v___f_2693_);
lean_dec(v_getEnv_2692_);
lean_dec(v_toBind_2691_);
v___x_2697_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2698_ = l_Lean_throwError___redArg(v_inst_2689_, v_inst_2690_, v___x_2697_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; 
lean_dec_ref(v_inst_2690_);
lean_dec_ref(v_inst_2689_);
v___x_2699_ = lean_apply_4(v_toBind_2691_, lean_box(0), lean_box(0), v_getEnv_2692_, v___f_2693_);
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_docs_2703_, lean_object* v_deferred_2704_){
_start:
{
lean_object* v_toBind_2705_; lean_object* v_getEnv_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; 
v_toBind_2705_ = lean_ctor_get(v_inst_2700_, 1);
lean_inc_n(v_toBind_2705_, 3);
v_getEnv_2706_ = lean_ctor_get(v_inst_2701_, 0);
lean_inc_n(v_getEnv_2706_, 3);
lean_inc_ref(v_inst_2702_);
lean_inc_ref(v_inst_2700_);
v___f_2707_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2707_, 0, v_docs_2703_);
lean_closure_set(v___f_2707_, 1, v_inst_2700_);
lean_closure_set(v___f_2707_, 2, v_inst_2702_);
lean_closure_set(v___f_2707_, 3, v_deferred_2704_);
lean_closure_set(v___f_2707_, 4, v_inst_2701_);
lean_closure_set(v___f_2707_, 5, v_toBind_2705_);
lean_closure_set(v___f_2707_, 6, v_getEnv_2706_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2708_, 0, v_inst_2700_);
lean_closure_set(v___f_2708_, 1, v_inst_2702_);
lean_closure_set(v___f_2708_, 2, v_toBind_2705_);
lean_closure_set(v___f_2708_, 3, v_getEnv_2706_);
lean_closure_set(v___f_2708_, 4, v___f_2707_);
v___x_2709_ = lean_apply_4(v_toBind_2705_, lean_box(0), lean_box(0), v_getEnv_2706_, v___f_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_docs_2715_, lean_object* v_deferred_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2711_, v_inst_2712_, v_inst_2714_, v_docs_2715_, v_deferred_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_docs_2723_, lean_object* v_deferred_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_addVersoModDocStringCore(v_m_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_docs_2723_, v_deferred_2724_);
lean_dec(v_inst_2721_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2726_, lean_object* v_as_2727_, size_t v_i_2728_, size_t v_stop_2729_, lean_object* v_b_2730_){
_start:
{
uint8_t v___x_2731_; 
v___x_2731_ = lean_usize_dec_eq(v_i_2728_, v_stop_2729_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v_index_2733_; lean_object* v_sourceString_2734_; lean_object* v_imports_2735_; lean_object* v_currNamespace_2736_; lean_object* v_openDecls_2737_; lean_object* v_options_2738_; lean_object* v_check_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2755_; 
v___x_2732_ = lean_array_uget(v_as_2727_, v_i_2728_);
v_index_2733_ = lean_ctor_get(v___x_2732_, 1);
v_sourceString_2734_ = lean_ctor_get(v___x_2732_, 2);
v_imports_2735_ = lean_ctor_get(v___x_2732_, 3);
v_currNamespace_2736_ = lean_ctor_get(v___x_2732_, 4);
v_openDecls_2737_ = lean_ctor_get(v___x_2732_, 5);
v_options_2738_ = lean_ctor_get(v___x_2732_, 6);
v_check_2739_ = lean_ctor_get(v___x_2732_, 7);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v___x_2732_, 0);
lean_dec(v_unused_2756_);
v___x_2741_ = v___x_2732_;
v_isShared_2742_ = v_isSharedCheck_2755_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_check_2739_);
lean_inc(v_options_2738_);
lean_inc(v_openDecls_2737_);
lean_inc(v_currNamespace_2736_);
lean_inc(v_imports_2735_);
lean_inc(v_sourceString_2734_);
lean_inc(v_index_2733_);
lean_dec(v___x_2732_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2755_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v_toEnvExtension_2744_; lean_object* v_asyncMode_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2743_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2744_ = lean_ctor_get(v___x_2743_, 0);
v_asyncMode_2745_ = lean_ctor_get(v_toEnvExtension_2744_, 2);
lean_inc(v_declName_2726_);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v_declName_2726_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2746_);
v___x_2748_ = v___x_2741_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_index_2733_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_sourceString_2734_);
lean_ctor_set(v_reuseFailAlloc_2754_, 3, v_imports_2735_);
lean_ctor_set(v_reuseFailAlloc_2754_, 4, v_currNamespace_2736_);
lean_ctor_set(v_reuseFailAlloc_2754_, 5, v_openDecls_2737_);
lean_ctor_set(v_reuseFailAlloc_2754_, 6, v_options_2738_);
lean_ctor_set(v_reuseFailAlloc_2754_, 7, v_check_2739_);
v___x_2748_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; size_t v___x_2751_; size_t v___x_2752_; 
v___x_2749_ = lean_box(0);
v___x_2750_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2743_, v_b_2730_, v___x_2748_, v_asyncMode_2745_, v___x_2749_);
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_add(v_i_2728_, v___x_2751_);
v_i_2728_ = v___x_2752_;
v_b_2730_ = v___x_2750_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2726_);
return v_b_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2757_, lean_object* v_as_2758_, lean_object* v_i_2759_, lean_object* v_stop_2760_, lean_object* v_b_2761_){
_start:
{
size_t v_i_boxed_2762_; size_t v_stop_boxed_2763_; lean_object* v_res_2764_; 
v_i_boxed_2762_ = lean_unbox_usize(v_i_2759_);
lean_dec(v_i_2759_);
v_stop_boxed_2763_ = lean_unbox_usize(v_stop_2760_);
lean_dec(v_stop_2760_);
v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2757_, v_as_2758_, v_i_boxed_2762_, v_stop_boxed_2763_, v_b_2761_);
lean_dec_ref(v_as_2758_);
return v_res_2764_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2765_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
return v___x_2767_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2771_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
lean_ctor_set(v___x_2771_, 2, v___x_2770_);
lean_ctor_set(v___x_2771_, 3, v___x_2770_);
lean_ctor_set(v___x_2771_, 4, v___x_2770_);
lean_ctor_set(v___x_2771_, 5, v___x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2772_, lean_object* v_docs_2773_, lean_object* v_deferred_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2814_; lean_object* v___y_2815_; uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_Name_isAnonymous(v_declName_2772_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v_env_2839_; lean_object* v___x_2840_; 
v___x_2838_ = lean_st_ref_get(v___y_2780_);
v_env_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc_ref(v_env_2839_);
lean_dec(v___x_2838_);
v___x_2840_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2839_, v_declName_2772_);
lean_dec_ref(v_env_2839_);
if (lean_obj_tag(v___x_2840_) == 0)
{
v___y_2814_ = v___y_2778_;
v___y_2815_ = v___y_2780_;
goto v___jp_2813_;
}
else
{
lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2855_; 
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2840_, 0);
lean_dec(v_unused_2856_);
v___x_2842_ = v___x_2840_;
v_isShared_2843_ = v_isSharedCheck_2855_;
goto v_resetjp_2841_;
}
else
{
lean_dec(v___x_2840_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2855_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (v___x_2837_ == 0)
{
lean_object* v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_dec_ref(v_docs_2773_);
v___x_2844_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2845_ = 1;
v___x_2846_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2772_, v___x_2845_);
v___x_2847_ = lean_string_append(v___x_2844_, v___x_2846_);
lean_dec_ref(v___x_2846_);
v___x_2848_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2849_ = lean_string_append(v___x_2847_, v___x_2848_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set_tag(v___x_2842_, 3);
lean_ctor_set(v___x_2842_, 0, v___x_2849_);
v___x_2851_ = v___x_2842_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = l_Lean_MessageData_ofFormat(v___x_2851_);
v___x_2853_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2852_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v___x_2853_;
}
}
else
{
lean_del_object(v___x_2842_);
v___y_2814_ = v___y_2778_;
v___y_2815_ = v___y_2780_;
goto v___jp_2813_;
}
}
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec_ref(v_docs_2773_);
lean_dec(v_declName_2772_);
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
return v___x_2858_;
}
v___jp_2782_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v_mctx_2797_; lean_object* v_zetaDeltaFVarIds_2798_; lean_object* v_postponed_2799_; lean_object* v_diag_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2811_; 
v___x_2793_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2794_, 0, v___y_2792_);
lean_ctor_set(v___x_2794_, 1, v___y_2785_);
lean_ctor_set(v___x_2794_, 2, v___y_2783_);
lean_ctor_set(v___x_2794_, 3, v___y_2790_);
lean_ctor_set(v___x_2794_, 4, v___y_2789_);
lean_ctor_set(v___x_2794_, 5, v___x_2793_);
lean_ctor_set(v___x_2794_, 6, v___y_2787_);
lean_ctor_set(v___x_2794_, 7, v___y_2791_);
lean_ctor_set(v___x_2794_, 8, v___y_2788_);
v___x_2795_ = lean_st_ref_set(v___y_2786_, v___x_2794_);
v___x_2796_ = lean_st_ref_take(v___y_2784_);
v_mctx_2797_ = lean_ctor_get(v___x_2796_, 0);
v_zetaDeltaFVarIds_2798_ = lean_ctor_get(v___x_2796_, 2);
v_postponed_2799_ = lean_ctor_get(v___x_2796_, 3);
v_diag_2800_ = lean_ctor_get(v___x_2796_, 4);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2811_ == 0)
{
lean_object* v_unused_2812_; 
v_unused_2812_ = lean_ctor_get(v___x_2796_, 1);
lean_dec(v_unused_2812_);
v___x_2802_ = v___x_2796_;
v_isShared_2803_ = v_isSharedCheck_2811_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_diag_2800_);
lean_inc(v_postponed_2799_);
lean_inc(v_zetaDeltaFVarIds_2798_);
lean_inc(v_mctx_2797_);
lean_dec(v___x_2796_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2811_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2804_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 1, v___x_2804_);
v___x_2806_ = v___x_2802_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_mctx_2797_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2810_, 2, v_zetaDeltaFVarIds_2798_);
lean_ctor_set(v_reuseFailAlloc_2810_, 3, v_postponed_2799_);
lean_ctor_set(v_reuseFailAlloc_2810_, 4, v_diag_2800_);
v___x_2806_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_st_ref_set(v___y_2784_, v___x_2806_);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
}
}
v___jp_2813_:
{
lean_object* v___x_2816_; lean_object* v_env_2817_; lean_object* v_nextMacroScope_2818_; lean_object* v_ngen_2819_; lean_object* v_auxDeclNGen_2820_; lean_object* v_traceState_2821_; lean_object* v_messages_2822_; lean_object* v_infoState_2823_; lean_object* v_snapshotTasks_2824_; lean_object* v___x_2825_; lean_object* v_env_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; 
v___x_2816_ = lean_st_ref_take(v___y_2815_);
v_env_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc_ref(v_env_2817_);
v_nextMacroScope_2818_ = lean_ctor_get(v___x_2816_, 1);
lean_inc(v_nextMacroScope_2818_);
v_ngen_2819_ = lean_ctor_get(v___x_2816_, 2);
lean_inc_ref(v_ngen_2819_);
v_auxDeclNGen_2820_ = lean_ctor_get(v___x_2816_, 3);
lean_inc_ref(v_auxDeclNGen_2820_);
v_traceState_2821_ = lean_ctor_get(v___x_2816_, 4);
lean_inc_ref(v_traceState_2821_);
v_messages_2822_ = lean_ctor_get(v___x_2816_, 6);
lean_inc_ref(v_messages_2822_);
v_infoState_2823_ = lean_ctor_get(v___x_2816_, 7);
lean_inc_ref(v_infoState_2823_);
v_snapshotTasks_2824_ = lean_ctor_get(v___x_2816_, 8);
lean_inc_ref(v_snapshotTasks_2824_);
lean_dec(v___x_2816_);
v___x_2825_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2772_);
v_env_2826_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2825_, v_env_2817_, v_declName_2772_, v_docs_2773_);
v___x_2827_ = lean_unsigned_to_nat(0u);
v___x_2828_ = lean_array_get_size(v_deferred_2774_);
v___x_2829_ = lean_nat_dec_lt(v___x_2827_, v___x_2828_);
if (v___x_2829_ == 0)
{
lean_dec(v_declName_2772_);
v___y_2783_ = v_ngen_2819_;
v___y_2784_ = v___y_2814_;
v___y_2785_ = v_nextMacroScope_2818_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v_messages_2822_;
v___y_2788_ = v_snapshotTasks_2824_;
v___y_2789_ = v_traceState_2821_;
v___y_2790_ = v_auxDeclNGen_2820_;
v___y_2791_ = v_infoState_2823_;
v___y_2792_ = v_env_2826_;
goto v___jp_2782_;
}
else
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_nat_dec_le(v___x_2828_, v___x_2828_);
if (v___x_2830_ == 0)
{
if (v___x_2829_ == 0)
{
lean_dec(v_declName_2772_);
v___y_2783_ = v_ngen_2819_;
v___y_2784_ = v___y_2814_;
v___y_2785_ = v_nextMacroScope_2818_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v_messages_2822_;
v___y_2788_ = v_snapshotTasks_2824_;
v___y_2789_ = v_traceState_2821_;
v___y_2790_ = v_auxDeclNGen_2820_;
v___y_2791_ = v_infoState_2823_;
v___y_2792_ = v_env_2826_;
goto v___jp_2782_;
}
else
{
size_t v___x_2831_; size_t v___x_2832_; lean_object* v___x_2833_; 
v___x_2831_ = ((size_t)0ULL);
v___x_2832_ = lean_usize_of_nat(v___x_2828_);
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2772_, v_deferred_2774_, v___x_2831_, v___x_2832_, v_env_2826_);
v___y_2783_ = v_ngen_2819_;
v___y_2784_ = v___y_2814_;
v___y_2785_ = v_nextMacroScope_2818_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v_messages_2822_;
v___y_2788_ = v_snapshotTasks_2824_;
v___y_2789_ = v_traceState_2821_;
v___y_2790_ = v_auxDeclNGen_2820_;
v___y_2791_ = v_infoState_2823_;
v___y_2792_ = v___x_2833_;
goto v___jp_2782_;
}
}
else
{
size_t v___x_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
v___x_2834_ = ((size_t)0ULL);
v___x_2835_ = lean_usize_of_nat(v___x_2828_);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2772_, v_deferred_2774_, v___x_2834_, v___x_2835_, v_env_2826_);
v___y_2783_ = v_ngen_2819_;
v___y_2784_ = v___y_2814_;
v___y_2785_ = v_nextMacroScope_2818_;
v___y_2786_ = v___y_2815_;
v___y_2787_ = v_messages_2822_;
v___y_2788_ = v_snapshotTasks_2824_;
v___y_2789_ = v_traceState_2821_;
v___y_2790_ = v_auxDeclNGen_2820_;
v___y_2791_ = v_infoState_2823_;
v___y_2792_ = v___x_2836_;
goto v___jp_2782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2859_, lean_object* v_docs_2860_, lean_object* v_deferred_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2859_, v_docs_2860_, v_deferred_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_deferred_2861_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2870_, lean_object* v_binders_2871_, lean_object* v_docComment_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___x_2900_; lean_object* v_env_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_st_ref_get(v_a_2878_);
v_env_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc_ref(v_env_2901_);
lean_dec(v___x_2900_);
v___x_2902_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2901_, v_declName_2870_);
lean_dec_ref(v_env_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
v___y_2881_ = v_a_2873_;
v___y_2882_ = v_a_2874_;
v___y_2883_ = v_a_2875_;
v___y_2884_ = v_a_2876_;
v___y_2885_ = v_a_2877_;
v___y_2886_ = v_a_2878_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_docComment_2872_);
lean_dec(v_binders_2871_);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2917_ == 0)
{
lean_object* v_unused_2918_; 
v_unused_2918_ = lean_ctor_get(v___x_2902_, 0);
lean_dec(v_unused_2918_);
v___x_2904_ = v___x_2902_;
v_isShared_2905_ = v_isSharedCheck_2917_;
goto v_resetjp_2903_;
}
else
{
lean_dec(v___x_2902_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2917_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2906_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2907_ = 1;
v___x_2908_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2870_, v___x_2907_);
v___x_2909_ = lean_string_append(v___x_2906_, v___x_2908_);
lean_dec_ref(v___x_2908_);
v___x_2910_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2911_ = lean_string_append(v___x_2909_, v___x_2910_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 3);
lean_ctor_set(v___x_2904_, 0, v___x_2911_);
v___x_2913_ = v___x_2904_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = l_Lean_MessageData_ofFormat(v___x_2913_);
v___x_2915_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2914_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
return v___x_2915_;
}
}
}
v___jp_2880_:
{
lean_object* v___x_2887_; 
lean_inc(v_declName_2870_);
v___x_2887_ = l_Lean_versoDocString(v_declName_2870_, v_binders_2871_, v_docComment_2872_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v_toVersoDocString_2889_; lean_object* v_deferredChecks_2890_; lean_object* v___x_2891_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v_toVersoDocString_2889_ = lean_ctor_get(v_a_2888_, 0);
lean_inc_ref(v_toVersoDocString_2889_);
v_deferredChecks_2890_ = lean_ctor_get(v_a_2888_, 1);
lean_inc_ref(v_deferredChecks_2890_);
lean_dec(v_a_2888_);
v___x_2891_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2870_, v_toVersoDocString_2889_, v_deferredChecks_2890_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec_ref(v_deferredChecks_2890_);
return v___x_2891_;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_declName_2870_);
v_a_2892_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2887_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2887_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2919_, lean_object* v_binders_2920_, lean_object* v_docComment_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_addVersoDocString(v_declName_2919_, v_binders_2920_, v_docComment_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2930_, lean_object* v_docComment_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___x_2959_; lean_object* v_env_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_st_ref_get(v_a_2937_);
v_env_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc_ref(v_env_2960_);
lean_dec(v___x_2959_);
v___x_2961_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2960_, v_declName_2930_);
lean_dec_ref(v_env_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
v___y_2940_ = v_a_2932_;
v___y_2941_ = v_a_2933_;
v___y_2942_ = v_a_2934_;
v___y_2943_ = v_a_2935_;
v___y_2944_ = v_a_2936_;
v___y_2945_ = v_a_2937_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v_docComment_2931_);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v___x_2961_, 0);
lean_dec(v_unused_2977_);
v___x_2963_ = v___x_2961_;
v_isShared_2964_ = v_isSharedCheck_2976_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v___x_2961_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2976_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; uint8_t v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2965_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2966_ = 1;
v___x_2967_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2930_, v___x_2966_);
v___x_2968_ = lean_string_append(v___x_2965_, v___x_2967_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 3);
lean_ctor_set(v___x_2963_, 0, v___x_2970_);
v___x_2972_ = v___x_2963_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = l_Lean_MessageData_ofFormat(v___x_2972_);
v___x_2974_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2973_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_);
return v___x_2974_;
}
}
}
v___jp_2939_:
{
lean_object* v___x_2946_; 
lean_inc(v_declName_2930_);
v___x_2946_ = l_Lean_versoDocStringFromString(v_declName_2930_, v_docComment_2931_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_toVersoDocString_2948_; lean_object* v_deferredChecks_2949_; lean_object* v___x_2950_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2946_, 1);
v_toVersoDocString_2948_ = lean_ctor_get(v_a_2947_, 0);
lean_inc_ref(v_toVersoDocString_2948_);
v_deferredChecks_2949_ = lean_ctor_get(v_a_2947_, 1);
lean_inc_ref(v_deferredChecks_2949_);
lean_dec(v_a_2947_);
v___x_2950_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2930_, v_toVersoDocString_2948_, v_deferredChecks_2949_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec_ref(v_deferredChecks_2949_);
return v___x_2950_;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec(v_declName_2930_);
v_a_2951_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2946_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2946_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2978_, lean_object* v_docComment_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_addVersoDocStringFromString(v_declName_2978_, v_docComment_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2988_, lean_object* v_msgData_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
uint8_t v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = 2;
v___x_2996_ = 0;
v___x_2997_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2988_, v_msgData_2989_, v___x_2995_, v___x_2996_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2998_, lean_object* v_msgData_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2998_, v_msgData_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v_ref_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3006_, lean_object* v_str_3007_, lean_object* v_as_3008_, size_t v_sz_3009_, size_t v_i_3010_, lean_object* v_b_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
lean_object* v_a_3020_; uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_lt(v_i_3010_, v_sz_3009_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_b_3011_);
return v___x_3025_;
}
else
{
lean_object* v_a_3026_; lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v_start_3029_; lean_object* v_stop_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3050_; 
v_a_3026_ = lean_array_uget_borrowed(v_as_3008_, v_i_3010_);
v_fst_3027_ = lean_ctor_get(v_a_3026_, 0);
lean_inc(v_fst_3027_);
v_snd_3028_ = lean_ctor_get(v_a_3026_, 1);
v_start_3029_ = lean_ctor_get(v_fst_3027_, 0);
v_stop_3030_ = lean_ctor_get(v_fst_3027_, 1);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_fst_3027_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3032_ = v_fst_3027_;
v_isShared_3033_ = v_isSharedCheck_3050_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_stop_3030_);
lean_inc(v_start_3029_);
lean_dec(v_fst_3027_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3050_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
if (lean_obj_tag(v___y_3006_) == 1)
{
lean_object* v_val_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v_val_3035_ = lean_ctor_get(v___y_3006_, 0);
v___x_3036_ = lean_nat_add(v_val_3035_, v_start_3029_);
v___x_3037_ = lean_nat_add(v_val_3035_, v_stop_3030_);
v___x_3038_ = 0;
v___x_3039_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3039_, 0, v___x_3036_);
lean_ctor_set(v___x_3039_, 1, v___x_3037_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*2, v___x_3038_);
v___x_3040_ = lean_string_utf8_extract(v_str_3007_, v_start_3029_, v_stop_3030_);
lean_dec(v_stop_3030_);
lean_dec(v_start_3029_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 2);
lean_ctor_set(v___x_3032_, 1, v___x_3040_);
lean_ctor_set(v___x_3032_, 0, v___x_3039_);
v___x_3042_ = v___x_3032_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_inc(v_snd_3028_);
v___x_3043_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_snd_3028_);
v___x_3044_ = l_Lean_MessageData_ofFormat(v___x_3043_);
v___x_3045_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3042_, v___x_3044_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec_ref(v___x_3042_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec_ref_known(v___x_3045_, 1);
v_a_3020_ = v___x_3034_;
goto v___jp_3019_;
}
else
{
return v___x_3045_;
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_del_object(v___x_3032_);
lean_dec(v_stop_3030_);
lean_dec(v_start_3029_);
lean_inc(v_snd_3028_);
v___x_3047_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_snd_3028_);
v___x_3048_ = l_Lean_MessageData_ofFormat(v___x_3047_);
v___x_3049_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3048_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_dec_ref_known(v___x_3049_, 1);
v_a_3020_ = v___x_3034_;
goto v___jp_3019_;
}
else
{
return v___x_3049_;
}
}
}
}
v___jp_3019_:
{
size_t v___x_3021_; size_t v___x_3022_; 
v___x_3021_ = ((size_t)1ULL);
v___x_3022_ = lean_usize_add(v_i_3010_, v___x_3021_);
v_i_3010_ = v___x_3022_;
v_b_3011_ = v_a_3020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3051_, lean_object* v_str_3052_, lean_object* v_as_3053_, lean_object* v_sz_3054_, lean_object* v_i_3055_, lean_object* v_b_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
size_t v_sz_boxed_3064_; size_t v_i_boxed_3065_; lean_object* v_res_3066_; 
v_sz_boxed_3064_ = lean_unbox_usize(v_sz_3054_);
lean_dec(v_sz_3054_);
v_i_boxed_3065_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3051_, v_str_3052_, v_as_3053_, v_sz_boxed_3064_, v_i_boxed_3065_, v_b_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec_ref(v_as_3053_);
lean_dec_ref(v_str_3052_);
lean_dec(v___y_3051_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_str_3075_; lean_object* v___y_3077_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v_str_3075_ = l_Lean_TSyntax_getDocString(v_docstring_3067_);
v___x_3092_ = lean_unsigned_to_nat(1u);
v___x_3093_ = l_Lean_Syntax_getArg(v_docstring_3067_, v___x_3092_);
v___x_3094_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3093_);
lean_dec(v___x_3093_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
v___y_3077_ = v___x_3095_;
goto v___jp_3076_;
}
else
{
lean_object* v_val_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; 
v_val_3096_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3097_ = 0;
v___x_3098_ = l_Lean_SourceInfo_getPos_x3f(v_val_3096_, v___x_3097_);
lean_dec(v_val_3096_);
v___y_3077_ = v___x_3098_;
goto v___jp_3076_;
}
v___jp_3076_:
{
lean_object* v___x_3078_; lean_object* v_fst_3079_; lean_object* v___x_3080_; size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
lean_inc_ref(v_str_3075_);
v___x_3078_ = l_Lean_rewriteManualLinksCore(v_str_3075_);
v_fst_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_fst_3079_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = lean_box(0);
v_sz_3081_ = lean_array_size(v_fst_3079_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3077_, v_str_3075_, v_fst_3079_, v_sz_3081_, v___x_3082_, v___x_3080_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v_fst_3079_);
lean_dec_ref(v_str_3075_);
lean_dec(v___y_3077_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3083_, 0);
lean_dec(v_unused_3091_);
v___x_3085_ = v___x_3083_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_dec(v___x_3083_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3080_);
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3080_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v_docstring_3099_);
return v_res_3107_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3110_ = l_Lean_stringToMessageData(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v_val_3126_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_unsigned_to_nat(1u);
v___x_3134_ = l_Lean_Syntax_getArg(v_stx_3111_, v___x_3133_);
switch(lean_obj_tag(v___x_3134_))
{
case 2:
{
lean_object* v_val_3135_; 
lean_dec(v_stx_3111_);
v_val_3135_ = lean_ctor_get(v___x_3134_, 1);
lean_inc_ref(v_val_3135_);
lean_dec_ref_known(v___x_3134_, 2);
v_val_3126_ = v_val_3135_;
goto v___jp_3125_;
}
case 1:
{
lean_object* v_kind_3136_; 
v_kind_3136_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_kind_3136_);
if (lean_obj_tag(v_kind_3136_) == 1)
{
lean_object* v_pre_3137_; 
v_pre_3137_ = lean_ctor_get(v_kind_3136_, 0);
lean_inc(v_pre_3137_);
if (lean_obj_tag(v_pre_3137_) == 1)
{
lean_object* v_pre_3138_; 
v_pre_3138_ = lean_ctor_get(v_pre_3137_, 0);
lean_inc(v_pre_3138_);
if (lean_obj_tag(v_pre_3138_) == 1)
{
lean_object* v_pre_3139_; 
v_pre_3139_ = lean_ctor_get(v_pre_3138_, 0);
lean_inc(v_pre_3139_);
if (lean_obj_tag(v_pre_3139_) == 1)
{
lean_object* v_pre_3140_; 
v_pre_3140_ = lean_ctor_get(v_pre_3139_, 0);
if (lean_obj_tag(v_pre_3140_) == 0)
{
lean_object* v_str_3141_; lean_object* v_str_3142_; lean_object* v_str_3143_; lean_object* v_str_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v_str_3141_ = lean_ctor_get(v_kind_3136_, 1);
lean_inc_ref(v_str_3141_);
lean_dec_ref_known(v_kind_3136_, 2);
v_str_3142_ = lean_ctor_get(v_pre_3137_, 1);
lean_inc_ref(v_str_3142_);
lean_dec_ref_known(v_pre_3137_, 2);
v_str_3143_ = lean_ctor_get(v_pre_3138_, 1);
lean_inc_ref(v_str_3143_);
lean_dec_ref_known(v_pre_3138_, 2);
v_str_3144_ = lean_ctor_get(v_pre_3139_, 1);
lean_inc_ref(v_str_3144_);
lean_dec_ref_known(v_pre_3139_, 2);
v___x_3145_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3146_ = lean_string_dec_eq(v_str_3144_, v___x_3145_);
lean_dec_ref(v_str_3144_);
if (v___x_3146_ == 0)
{
lean_dec_ref(v_str_3143_);
lean_dec_ref(v_str_3142_);
lean_dec_ref(v_str_3141_);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3147_; uint8_t v___x_3148_; 
v___x_3147_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3148_ = lean_string_dec_eq(v_str_3143_, v___x_3147_);
lean_dec_ref(v_str_3143_);
if (v___x_3148_ == 0)
{
lean_dec_ref(v_str_3142_);
lean_dec_ref(v_str_3141_);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
v___x_3149_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3150_ = lean_string_dec_eq(v_str_3142_, v___x_3149_);
lean_dec_ref(v_str_3142_);
if (v___x_3150_ == 0)
{
lean_dec_ref(v_str_3141_);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3151_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3152_ = lean_string_dec_eq(v_str_3141_, v___x_3151_);
lean_dec_ref(v_str_3141_);
if (v___x_3152_ == 0)
{
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = l_Lean_Syntax_getArg(v___x_3134_, v___x_3153_);
lean_dec_ref_known(v___x_3134_, 3);
if (lean_obj_tag(v___x_3154_) == 2)
{
lean_object* v_val_3155_; 
lean_dec(v_stx_3111_);
v_val_3155_ = lean_ctor_get(v___x_3154_, 1);
lean_inc_ref(v_val_3155_);
lean_dec_ref_known(v___x_3154_, 2);
v_val_3126_ = v_val_3155_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_dec(v___x_3154_);
v___x_3156_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3111_);
v___x_3157_ = l_Lean_MessageData_ofSyntax(v_stx_3111_);
v___x_3158_ = l_Lean_indentD(v___x_3157_);
v___x_3159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3156_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3111_, v___x_3159_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v_stx_3111_);
return v___x_3160_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3139_, 2);
lean_dec_ref_known(v_pre_3138_, 2);
lean_dec_ref_known(v_pre_3137_, 2);
lean_dec_ref_known(v_kind_3136_, 2);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
}
else
{
lean_dec_ref_known(v_pre_3138_, 2);
lean_dec(v_pre_3139_);
lean_dec_ref_known(v_pre_3137_, 2);
lean_dec_ref_known(v_kind_3136_, 2);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
}
else
{
lean_dec(v_pre_3138_);
lean_dec_ref_known(v_pre_3137_, 2);
lean_dec_ref_known(v_kind_3136_, 2);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
}
else
{
lean_dec(v_pre_3137_);
lean_dec_ref_known(v_kind_3136_, 2);
lean_dec_ref_known(v___x_3134_, 3);
goto v___jp_3119_;
}
}
else
{
lean_dec_ref_known(v___x_3134_, 3);
lean_dec(v_kind_3136_);
goto v___jp_3119_;
}
}
default: 
{
lean_dec(v___x_3134_);
goto v___jp_3119_;
}
}
v___jp_3119_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3120_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3111_);
v___x_3121_ = l_Lean_MessageData_ofSyntax(v_stx_3111_);
v___x_3122_ = l_Lean_indentD(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3120_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3111_, v___x_3123_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v_stx_3111_);
return v___x_3124_;
}
v___jp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_string_utf8_byte_size(v_val_3126_);
v___x_3129_ = lean_unsigned_to_nat(2u);
v___x_3130_ = lean_nat_sub(v___x_3128_, v___x_3129_);
v___x_3131_ = lean_string_utf8_extract(v_val_3126_, v___x_3127_, v___x_3130_);
lean_dec(v___x_3130_);
lean_dec_ref(v_val_3126_);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3170_, lean_object* v_docComment_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v___x_3242_; 
v___x_3242_ = l_Lean_Name_isAnonymous(v_declName_3170_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v_env_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_st_ref_get(v___y_3177_);
v_env_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref(v_env_3244_);
lean_dec(v___x_3243_);
v___x_3245_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3244_, v_declName_3170_);
lean_dec_ref(v_env_3244_);
if (lean_obj_tag(v___x_3245_) == 0)
{
v___y_3180_ = v___y_3172_;
v___y_3181_ = v___y_3173_;
v___y_3182_ = v___y_3174_;
v___y_3183_ = v___y_3175_;
v___y_3184_ = v___y_3176_;
v___y_3185_ = v___y_3177_;
goto v___jp_3179_;
}
else
{
lean_dec_ref_known(v___x_3245_, 1);
if (v___x_3242_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v_docComment_3171_);
v___x_3246_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3247_ = l_Lean_MessageData_ofConstName(v_declName_3170_, v___x_3242_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3250_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
return v___x_3251_;
}
else
{
v___y_3180_ = v___y_3172_;
v___y_3181_ = v___y_3173_;
v___y_3182_ = v___y_3174_;
v___y_3183_ = v___y_3175_;
v___y_3184_ = v___y_3176_;
v___y_3185_ = v___y_3177_;
goto v___jp_3179_;
}
}
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_docComment_3171_);
lean_dec(v_declName_3170_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3252_);
return v___x_3253_;
}
v___jp_3179_:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3171_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v___x_3187_; 
lean_dec_ref_known(v___x_3186_, 1);
v___x_3187_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3171_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3233_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3233_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3233_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v_env_3193_; lean_object* v_nextMacroScope_3194_; lean_object* v_ngen_3195_; lean_object* v_auxDeclNGen_3196_; lean_object* v_traceState_3197_; lean_object* v_messages_3198_; lean_object* v_infoState_3199_; lean_object* v_snapshotTasks_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3231_; 
v___x_3192_ = lean_st_ref_take(v___y_3185_);
v_env_3193_ = lean_ctor_get(v___x_3192_, 0);
v_nextMacroScope_3194_ = lean_ctor_get(v___x_3192_, 1);
v_ngen_3195_ = lean_ctor_get(v___x_3192_, 2);
v_auxDeclNGen_3196_ = lean_ctor_get(v___x_3192_, 3);
v_traceState_3197_ = lean_ctor_get(v___x_3192_, 4);
v_messages_3198_ = lean_ctor_get(v___x_3192_, 6);
v_infoState_3199_ = lean_ctor_get(v___x_3192_, 7);
v_snapshotTasks_3200_ = lean_ctor_get(v___x_3192_, 8);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3192_, 5);
lean_dec(v_unused_3232_);
v___x_3202_ = v___x_3192_;
v_isShared_3203_ = v_isSharedCheck_3231_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snapshotTasks_3200_);
lean_inc(v_infoState_3199_);
lean_inc(v_messages_3198_);
lean_inc(v_traceState_3197_);
lean_inc(v_auxDeclNGen_3196_);
lean_inc(v_ngen_3195_);
lean_inc(v_nextMacroScope_3194_);
lean_inc(v_env_3193_);
lean_dec(v___x_3192_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3231_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3204_ = l_Lean_docStringExt;
v___x_3205_ = l_String_removeLeadingSpaces(v_a_3188_);
v___x_3206_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3204_, v_env_3193_, v_declName_3170_, v___x_3205_);
v___x_3207_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 5, v___x_3207_);
lean_ctor_set(v___x_3202_, 0, v___x_3206_);
v___x_3209_ = v___x_3202_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_nextMacroScope_3194_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_ngen_3195_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_auxDeclNGen_3196_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v_traceState_3197_);
lean_ctor_set(v_reuseFailAlloc_3230_, 5, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3230_, 6, v_messages_3198_);
lean_ctor_set(v_reuseFailAlloc_3230_, 7, v_infoState_3199_);
lean_ctor_set(v_reuseFailAlloc_3230_, 8, v_snapshotTasks_3200_);
v___x_3209_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_mctx_3212_; lean_object* v_zetaDeltaFVarIds_3213_; lean_object* v_postponed_3214_; lean_object* v_diag_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3228_; 
v___x_3210_ = lean_st_ref_set(v___y_3185_, v___x_3209_);
v___x_3211_ = lean_st_ref_take(v___y_3183_);
v_mctx_3212_ = lean_ctor_get(v___x_3211_, 0);
v_zetaDeltaFVarIds_3213_ = lean_ctor_get(v___x_3211_, 2);
v_postponed_3214_ = lean_ctor_get(v___x_3211_, 3);
v_diag_3215_ = lean_ctor_get(v___x_3211_, 4);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3211_, 1);
lean_dec(v_unused_3229_);
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3228_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_diag_3215_);
lean_inc(v_postponed_3214_);
lean_inc(v_zetaDeltaFVarIds_3213_);
lean_inc(v_mctx_3212_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3228_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 1, v___x_3219_);
v___x_3221_ = v___x_3217_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_mctx_3212_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_zetaDeltaFVarIds_3213_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_postponed_3214_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_diag_3215_);
v___x_3221_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3222_ = lean_st_ref_set(v___y_3183_, v___x_3221_);
v___x_3223_ = lean_box(0);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3223_);
v___x_3225_ = v___x_3190_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
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
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_declName_3170_);
v_a_3234_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3187_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3187_);
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
}
else
{
lean_dec(v_docComment_3171_);
lean_dec(v_declName_3170_);
return v___x_3186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3254_, lean_object* v_docComment_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3254_, v_docComment_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3264_, lean_object* v_declName_3265_, lean_object* v_binders_3266_, lean_object* v_docComment_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
if (v_isVerso_3264_ == 0)
{
lean_object* v___x_3275_; 
lean_dec(v_binders_3266_);
v___x_3275_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3265_, v_docComment_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_addVersoDocString(v_declName_3265_, v_binders_3266_, v_docComment_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3277_, lean_object* v_declName_3278_, lean_object* v_binders_3279_, lean_object* v_docComment_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
uint8_t v_isVerso_boxed_3288_; lean_object* v_res_3289_; 
v_isVerso_boxed_3288_ = lean_unbox(v_isVerso_3277_);
v_res_3289_ = l_Lean_addDocStringOf(v_isVerso_boxed_3288_, v_declName_3278_, v_binders_3279_, v_docComment_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3290_, lean_object* v_msgData_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3290_, v_msgData_3291_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3300_, lean_object* v_msgData_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3300_, v_msgData_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_ref_3300_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3310_, lean_object* v_t_3311_){
_start:
{
if (lean_obj_tag(v_t_3311_) == 0)
{
lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v_l_3314_; lean_object* v_r_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3969_; 
v_k_3312_ = lean_ctor_get(v_t_3311_, 1);
v_v_3313_ = lean_ctor_get(v_t_3311_, 2);
v_l_3314_ = lean_ctor_get(v_t_3311_, 3);
v_r_3315_ = lean_ctor_get(v_t_3311_, 4);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_t_3311_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; 
v_unused_3970_ = lean_ctor_get(v_t_3311_, 0);
lean_dec(v_unused_3970_);
v___x_3317_ = v_t_3311_;
v_isShared_3318_ = v_isSharedCheck_3969_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_r_3315_);
lean_inc(v_l_3314_);
lean_inc(v_v_3313_);
lean_inc(v_k_3312_);
lean_dec(v_t_3311_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3969_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
uint8_t v___x_3319_; 
v___x_3319_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3310_, v_k_3312_);
switch(v___x_3319_)
{
case 0:
{
lean_object* v_impl_3320_; lean_object* v___x_3321_; 
v_impl_3320_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3310_, v_l_3314_);
v___x_3321_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3320_) == 0)
{
if (lean_obj_tag(v_r_3315_) == 0)
{
lean_object* v_size_3322_; lean_object* v_size_3323_; lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v_l_3326_; lean_object* v_r_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
v_size_3322_ = lean_ctor_get(v_impl_3320_, 0);
lean_inc(v_size_3322_);
v_size_3323_ = lean_ctor_get(v_r_3315_, 0);
v_k_3324_ = lean_ctor_get(v_r_3315_, 1);
v_v_3325_ = lean_ctor_get(v_r_3315_, 2);
v_l_3326_ = lean_ctor_get(v_r_3315_, 3);
lean_inc(v_l_3326_);
v_r_3327_ = lean_ctor_get(v_r_3315_, 4);
v___x_3328_ = lean_unsigned_to_nat(3u);
v___x_3329_ = lean_nat_mul(v___x_3328_, v_size_3322_);
v___x_3330_ = lean_nat_dec_lt(v___x_3329_, v_size_3323_);
lean_dec(v___x_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
lean_dec(v_l_3326_);
v___x_3331_ = lean_nat_add(v___x_3321_, v_size_3322_);
lean_dec(v_size_3322_);
v___x_3332_ = lean_nat_add(v___x_3331_, v_size_3323_);
lean_dec(v___x_3331_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 3, v_impl_3320_);
lean_ctor_set(v___x_3317_, 0, v___x_3332_);
v___x_3334_ = v___x_3317_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_impl_3320_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_r_3315_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
else
{
lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3399_; 
lean_inc(v_r_3327_);
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
lean_inc(v_size_3323_);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; 
v_unused_3400_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_r_3315_, 2);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_r_3315_, 1);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3404_);
v___x_3337_ = v_r_3315_;
v_isShared_3338_ = v_isSharedCheck_3399_;
goto v_resetjp_3336_;
}
else
{
lean_dec(v_r_3315_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3399_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_size_3339_; lean_object* v_k_3340_; lean_object* v_v_3341_; lean_object* v_l_3342_; lean_object* v_r_3343_; lean_object* v_size_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_size_3339_ = lean_ctor_get(v_l_3326_, 0);
v_k_3340_ = lean_ctor_get(v_l_3326_, 1);
v_v_3341_ = lean_ctor_get(v_l_3326_, 2);
v_l_3342_ = lean_ctor_get(v_l_3326_, 3);
v_r_3343_ = lean_ctor_get(v_l_3326_, 4);
v_size_3344_ = lean_ctor_get(v_r_3327_, 0);
v___x_3345_ = lean_unsigned_to_nat(2u);
v___x_3346_ = lean_nat_mul(v___x_3345_, v_size_3344_);
v___x_3347_ = lean_nat_dec_lt(v_size_3339_, v___x_3346_);
lean_dec(v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3375_; 
lean_inc(v_r_3343_);
lean_inc(v_l_3342_);
lean_inc(v_v_3341_);
lean_inc(v_k_3340_);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_l_3326_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; lean_object* v_unused_3379_; lean_object* v_unused_3380_; 
v_unused_3376_ = lean_ctor_get(v_l_3326_, 4);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_l_3326_, 3);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_l_3326_, 2);
lean_dec(v_unused_3378_);
v_unused_3379_ = lean_ctor_get(v_l_3326_, 1);
lean_dec(v_unused_3379_);
v_unused_3380_ = lean_ctor_get(v_l_3326_, 0);
lean_dec(v_unused_3380_);
v___x_3349_ = v_l_3326_;
v_isShared_3350_ = v_isSharedCheck_3375_;
goto v_resetjp_3348_;
}
else
{
lean_dec(v_l_3326_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3375_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3365_; 
v___x_3351_ = lean_nat_add(v___x_3321_, v_size_3322_);
lean_dec(v_size_3322_);
v___x_3352_ = lean_nat_add(v___x_3351_, v_size_3323_);
lean_dec(v_size_3323_);
if (lean_obj_tag(v_l_3342_) == 0)
{
lean_object* v_size_3373_; 
v_size_3373_ = lean_ctor_get(v_l_3342_, 0);
lean_inc(v_size_3373_);
v___y_3365_ = v_size_3373_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_unsigned_to_nat(0u);
v___y_3365_ = v___x_3374_;
goto v___jp_3364_;
}
v___jp_3353_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_nat_add(v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 4, v_r_3327_);
lean_ctor_set(v___x_3349_, 3, v_r_3343_);
lean_ctor_set(v___x_3349_, 2, v_v_3325_);
lean_ctor_set(v___x_3349_, 1, v_k_3324_);
lean_ctor_set(v___x_3349_, 0, v___x_3357_);
v___x_3359_ = v___x_3349_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3343_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3327_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v___x_3359_);
lean_ctor_set(v___x_3337_, 3, v___y_3354_);
lean_ctor_set(v___x_3337_, 2, v_v_3341_);
lean_ctor_set(v___x_3337_, 1, v_k_3340_);
lean_ctor_set(v___x_3337_, 0, v___x_3352_);
v___x_3361_ = v___x_3337_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3352_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3340_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3341_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___y_3354_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3359_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
v___jp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_nat_add(v___x_3351_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec(v___x_3351_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_l_3342_);
lean_ctor_set(v___x_3317_, 3, v_impl_3320_);
lean_ctor_set(v___x_3317_, 0, v___x_3366_);
v___x_3368_ = v___x_3317_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3372_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3372_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3372_, 3, v_impl_3320_);
lean_ctor_set(v_reuseFailAlloc_3372_, 4, v_l_3342_);
v___x_3368_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_nat_add(v___x_3321_, v_size_3344_);
if (lean_obj_tag(v_r_3343_) == 0)
{
lean_object* v_size_3370_; 
v_size_3370_ = lean_ctor_get(v_r_3343_, 0);
lean_inc(v_size_3370_);
v___y_3354_ = v___x_3368_;
v___y_3355_ = v___x_3369_;
v___y_3356_ = v_size_3370_;
goto v___jp_3353_;
}
else
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_unsigned_to_nat(0u);
v___y_3354_ = v___x_3368_;
v___y_3355_ = v___x_3369_;
v___y_3356_ = v___x_3371_;
goto v___jp_3353_;
}
}
}
}
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_del_object(v___x_3317_);
v___x_3381_ = lean_nat_add(v___x_3321_, v_size_3322_);
lean_dec(v_size_3322_);
v___x_3382_ = lean_nat_add(v___x_3381_, v_size_3323_);
lean_dec(v_size_3323_);
v___x_3383_ = lean_nat_add(v___x_3381_, v_size_3339_);
lean_dec(v___x_3381_);
lean_inc_ref(v_impl_3320_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 4, v_l_3326_);
lean_ctor_set(v___x_3337_, 3, v_impl_3320_);
lean_ctor_set(v___x_3337_, 2, v_v_3313_);
lean_ctor_set(v___x_3337_, 1, v_k_3312_);
lean_ctor_set(v___x_3337_, 0, v___x_3383_);
v___x_3385_ = v___x_3337_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3398_, 3, v_impl_3320_);
lean_ctor_set(v_reuseFailAlloc_3398_, 4, v_l_3326_);
v___x_3385_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_isSharedCheck_3392_ = !lean_is_exclusive(v_impl_3320_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; lean_object* v_unused_3397_; 
v_unused_3393_ = lean_ctor_get(v_impl_3320_, 4);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_impl_3320_, 3);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_impl_3320_, 2);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_impl_3320_, 1);
lean_dec(v_unused_3396_);
v_unused_3397_ = lean_ctor_get(v_impl_3320_, 0);
lean_dec(v_unused_3397_);
v___x_3387_ = v_impl_3320_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v_impl_3320_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_r_3327_);
lean_ctor_set(v___x_3387_, 3, v___x_3385_);
lean_ctor_set(v___x_3387_, 2, v_v_3325_);
lean_ctor_set(v___x_3387_, 1, v_k_3324_);
lean_ctor_set(v___x_3387_, 0, v___x_3382_);
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3391_, 4, v_r_3327_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_size_3405_ = lean_ctor_get(v_impl_3320_, 0);
lean_inc(v_size_3405_);
v___x_3406_ = lean_nat_add(v___x_3321_, v_size_3405_);
lean_dec(v_size_3405_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 3, v_impl_3320_);
lean_ctor_set(v___x_3317_, 0, v___x_3406_);
v___x_3408_ = v___x_3317_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3409_, 3, v_impl_3320_);
lean_ctor_set(v_reuseFailAlloc_3409_, 4, v_r_3315_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
else
{
if (lean_obj_tag(v_r_3315_) == 0)
{
lean_object* v_l_3410_; 
v_l_3410_ = lean_ctor_get(v_r_3315_, 3);
lean_inc(v_l_3410_);
if (lean_obj_tag(v_l_3410_) == 0)
{
lean_object* v_r_3411_; 
v_r_3411_ = lean_ctor_get(v_r_3315_, 4);
lean_inc(v_r_3411_);
if (lean_obj_tag(v_r_3411_) == 0)
{
lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3427_; 
v_size_3412_ = lean_ctor_get(v_r_3315_, 0);
v_k_3413_ = lean_ctor_get(v_r_3315_, 1);
v_v_3414_ = lean_ctor_get(v_r_3315_, 2);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; lean_object* v_unused_3429_; 
v_unused_3428_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3429_);
v___x_3416_ = v_r_3315_;
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_v_3414_);
lean_inc(v_k_3413_);
lean_inc(v_size_3412_);
lean_dec(v_r_3315_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3427_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_size_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v_size_3418_ = lean_ctor_get(v_l_3410_, 0);
v___x_3419_ = lean_nat_add(v___x_3321_, v_size_3412_);
lean_dec(v_size_3412_);
v___x_3420_ = lean_nat_add(v___x_3321_, v_size_3418_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 4, v_l_3410_);
lean_ctor_set(v___x_3416_, 3, v_impl_3320_);
lean_ctor_set(v___x_3416_, 2, v_v_3313_);
lean_ctor_set(v___x_3416_, 1, v_k_3312_);
lean_ctor_set(v___x_3416_, 0, v___x_3420_);
v___x_3422_ = v___x_3416_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_impl_3320_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v_l_3410_);
v___x_3422_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3424_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_r_3411_);
lean_ctor_set(v___x_3317_, 3, v___x_3422_);
lean_ctor_set(v___x_3317_, 2, v_v_3414_);
lean_ctor_set(v___x_3317_, 1, v_k_3413_);
lean_ctor_set(v___x_3317_, 0, v___x_3419_);
v___x_3424_ = v___x_3317_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3419_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3413_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_v_3414_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_r_3411_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_object* v_k_3430_; lean_object* v_v_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3454_; 
v_k_3430_ = lean_ctor_get(v_r_3315_, 1);
v_v_3431_ = lean_ctor_get(v_r_3315_, 2);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3455_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3457_);
v___x_3433_ = v_r_3315_;
v_isShared_3434_ = v_isSharedCheck_3454_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_v_3431_);
lean_inc(v_k_3430_);
lean_dec(v_r_3315_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3454_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_k_3435_; lean_object* v_v_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3450_; 
v_k_3435_ = lean_ctor_get(v_l_3410_, 1);
v_v_3436_ = lean_ctor_get(v_l_3410_, 2);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_l_3410_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3451_ = lean_ctor_get(v_l_3410_, 4);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_l_3410_, 3);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_l_3410_, 0);
lean_dec(v_unused_3453_);
v___x_3438_ = v_l_3410_;
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_v_3436_);
lean_inc(v_k_3435_);
lean_dec(v_l_3410_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3450_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_unsigned_to_nat(3u);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 4, v_r_3411_);
lean_ctor_set(v___x_3438_, 3, v_r_3411_);
lean_ctor_set(v___x_3438_, 2, v_v_3313_);
lean_ctor_set(v___x_3438_, 1, v_k_3312_);
lean_ctor_set(v___x_3438_, 0, v___x_3321_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_r_3411_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_r_3411_);
v___x_3442_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 3, v_r_3411_);
lean_ctor_set(v___x_3433_, 0, v___x_3321_);
v___x_3444_ = v___x_3433_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3430_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3431_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_r_3411_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v_r_3411_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v___x_3444_);
lean_ctor_set(v___x_3317_, 3, v___x_3442_);
lean_ctor_set(v___x_3317_, 2, v_v_3436_);
lean_ctor_set(v___x_3317_, 1, v_k_3435_);
lean_ctor_set(v___x_3317_, 0, v___x_3440_);
v___x_3446_ = v___x_3317_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_3435_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_3436_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3458_; 
v_r_3458_ = lean_ctor_get(v_r_3315_, 4);
lean_inc(v_r_3458_);
if (lean_obj_tag(v_r_3458_) == 0)
{
lean_object* v_k_3459_; lean_object* v_v_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3471_; 
v_k_3459_ = lean_ctor_get(v_r_3315_, 1);
v_v_3460_ = lean_ctor_get(v_r_3315_, 2);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; lean_object* v_unused_3473_; lean_object* v_unused_3474_; 
v_unused_3472_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3473_);
v_unused_3474_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3474_);
v___x_3462_ = v_r_3315_;
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_v_3460_);
lean_inc(v_k_3459_);
lean_dec(v_r_3315_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3471_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
v___x_3464_ = lean_unsigned_to_nat(3u);
if (v_isShared_3463_ == 0)
{
lean_ctor_set(v___x_3462_, 4, v_l_3410_);
lean_ctor_set(v___x_3462_, 2, v_v_3313_);
lean_ctor_set(v___x_3462_, 1, v_k_3312_);
lean_ctor_set(v___x_3462_, 0, v___x_3321_);
v___x_3466_ = v___x_3462_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_l_3410_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_l_3410_);
v___x_3466_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3468_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_r_3458_);
lean_ctor_set(v___x_3317_, 3, v___x_3466_);
lean_ctor_set(v___x_3317_, 2, v_v_3460_);
lean_ctor_set(v___x_3317_, 1, v_k_3459_);
lean_ctor_set(v___x_3317_, 0, v___x_3464_);
v___x_3468_ = v___x_3317_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3459_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3460_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_r_3458_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
else
{
lean_object* v_size_3475_; lean_object* v_k_3476_; lean_object* v_v_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3488_; 
v_size_3475_ = lean_ctor_get(v_r_3315_, 0);
v_k_3476_ = lean_ctor_get(v_r_3315_, 1);
v_v_3477_ = lean_ctor_get(v_r_3315_, 2);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; lean_object* v_unused_3490_; 
v_unused_3489_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3490_);
v___x_3479_ = v_r_3315_;
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_v_3477_);
lean_inc(v_k_3476_);
lean_inc(v_size_3475_);
lean_dec(v_r_3315_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 3, v_r_3458_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_size_3475_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_r_3458_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_r_3458_);
v___x_3482_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_unsigned_to_nat(2u);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v___x_3482_);
lean_ctor_set(v___x_3317_, 3, v_r_3458_);
lean_ctor_set(v___x_3317_, 0, v___x_3483_);
v___x_3485_ = v___x_3317_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_r_3458_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3482_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
}
else
{
lean_object* v___x_3492_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 3, v_r_3315_);
lean_ctor_set(v___x_3317_, 0, v___x_3321_);
v___x_3492_ = v___x_3317_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_r_3315_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3317_);
lean_dec(v_v_3313_);
lean_dec(v_k_3312_);
if (lean_obj_tag(v_l_3314_) == 0)
{
if (lean_obj_tag(v_r_3315_) == 0)
{
lean_object* v_size_3494_; lean_object* v_k_3495_; lean_object* v_v_3496_; lean_object* v_l_3497_; lean_object* v_r_3498_; lean_object* v_size_3499_; lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v_l_3502_; lean_object* v_r_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v_size_3494_ = lean_ctor_get(v_l_3314_, 0);
v_k_3495_ = lean_ctor_get(v_l_3314_, 1);
v_v_3496_ = lean_ctor_get(v_l_3314_, 2);
v_l_3497_ = lean_ctor_get(v_l_3314_, 3);
v_r_3498_ = lean_ctor_get(v_l_3314_, 4);
lean_inc(v_r_3498_);
v_size_3499_ = lean_ctor_get(v_r_3315_, 0);
v_k_3500_ = lean_ctor_get(v_r_3315_, 1);
v_v_3501_ = lean_ctor_get(v_r_3315_, 2);
v_l_3502_ = lean_ctor_get(v_r_3315_, 3);
lean_inc(v_l_3502_);
v_r_3503_ = lean_ctor_get(v_r_3315_, 4);
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = lean_nat_dec_lt(v_size_3494_, v_size_3499_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3641_; 
lean_inc(v_l_3497_);
lean_inc(v_v_3496_);
lean_inc(v_k_3495_);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; lean_object* v_unused_3643_; lean_object* v_unused_3644_; lean_object* v_unused_3645_; lean_object* v_unused_3646_; 
v_unused_3642_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3642_);
v_unused_3643_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v_l_3314_, 2);
lean_dec(v_unused_3644_);
v_unused_3645_ = lean_ctor_get(v_l_3314_, 1);
lean_dec(v_unused_3645_);
v_unused_3646_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3646_);
v___x_3507_ = v_l_3314_;
v_isShared_3508_ = v_isSharedCheck_3641_;
goto v_resetjp_3506_;
}
else
{
lean_dec(v_l_3314_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3641_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v_tree_3510_; 
v___x_3509_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3495_, v_v_3496_, v_l_3497_, v_r_3498_);
v_tree_3510_ = lean_ctor_get(v___x_3509_, 2);
lean_inc(v_tree_3510_);
if (lean_obj_tag(v_tree_3510_) == 0)
{
lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v_size_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v_k_3511_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_k_3511_);
v_v_3512_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_v_3512_);
lean_dec_ref(v___x_3509_);
v_size_3513_ = lean_ctor_get(v_tree_3510_, 0);
v___x_3514_ = lean_unsigned_to_nat(3u);
v___x_3515_ = lean_nat_mul(v___x_3514_, v_size_3513_);
v___x_3516_ = lean_nat_dec_lt(v___x_3515_, v_size_3499_);
lean_dec(v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3520_; 
lean_dec(v_l_3502_);
v___x_3517_ = lean_nat_add(v___x_3504_, v_size_3513_);
v___x_3518_ = lean_nat_add(v___x_3517_, v_size_3499_);
lean_dec(v___x_3517_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v_r_3315_);
lean_ctor_set(v___x_3507_, 3, v_tree_3510_);
lean_ctor_set(v___x_3507_, 2, v_v_3512_);
lean_ctor_set(v___x_3507_, 1, v_k_3511_);
lean_ctor_set(v___x_3507_, 0, v___x_3518_);
v___x_3520_ = v___x_3507_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_tree_3510_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_r_3315_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
else
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3576_; 
lean_inc(v_r_3503_);
lean_inc(v_v_3501_);
lean_inc(v_k_3500_);
lean_inc(v_size_3499_);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; 
v_unused_3577_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_r_3315_, 2);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_r_3315_, 1);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3581_);
v___x_3523_ = v_r_3315_;
v_isShared_3524_ = v_isSharedCheck_3576_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_r_3315_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3576_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v_size_3525_; lean_object* v_k_3526_; lean_object* v_v_3527_; lean_object* v_l_3528_; lean_object* v_r_3529_; lean_object* v_size_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_size_3525_ = lean_ctor_get(v_l_3502_, 0);
v_k_3526_ = lean_ctor_get(v_l_3502_, 1);
v_v_3527_ = lean_ctor_get(v_l_3502_, 2);
v_l_3528_ = lean_ctor_get(v_l_3502_, 3);
v_r_3529_ = lean_ctor_get(v_l_3502_, 4);
v_size_3530_ = lean_ctor_get(v_r_3503_, 0);
v___x_3531_ = lean_unsigned_to_nat(2u);
v___x_3532_ = lean_nat_mul(v___x_3531_, v_size_3530_);
v___x_3533_ = lean_nat_dec_lt(v_size_3525_, v___x_3532_);
lean_dec(v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3561_; 
lean_inc(v_r_3529_);
lean_inc(v_l_3528_);
lean_inc(v_v_3527_);
lean_inc(v_k_3526_);
v_isSharedCheck_3561_ = !lean_is_exclusive(v_l_3502_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; lean_object* v_unused_3563_; lean_object* v_unused_3564_; lean_object* v_unused_3565_; lean_object* v_unused_3566_; 
v_unused_3562_ = lean_ctor_get(v_l_3502_, 4);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_l_3502_, 3);
lean_dec(v_unused_3563_);
v_unused_3564_ = lean_ctor_get(v_l_3502_, 2);
lean_dec(v_unused_3564_);
v_unused_3565_ = lean_ctor_get(v_l_3502_, 1);
lean_dec(v_unused_3565_);
v_unused_3566_ = lean_ctor_get(v_l_3502_, 0);
lean_dec(v_unused_3566_);
v___x_3535_ = v_l_3502_;
v_isShared_3536_ = v_isSharedCheck_3561_;
goto v_resetjp_3534_;
}
else
{
lean_dec(v_l_3502_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3561_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3551_; 
v___x_3537_ = lean_nat_add(v___x_3504_, v_size_3513_);
v___x_3538_ = lean_nat_add(v___x_3537_, v_size_3499_);
lean_dec(v_size_3499_);
if (lean_obj_tag(v_l_3528_) == 0)
{
lean_object* v_size_3559_; 
v_size_3559_ = lean_ctor_get(v_l_3528_, 0);
lean_inc(v_size_3559_);
v___y_3551_ = v_size_3559_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_unsigned_to_nat(0u);
v___y_3551_ = v___x_3560_;
goto v___jp_3550_;
}
v___jp_3539_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = lean_nat_add(v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 4, v_r_3503_);
lean_ctor_set(v___x_3535_, 3, v_r_3529_);
lean_ctor_set(v___x_3535_, 2, v_v_3501_);
lean_ctor_set(v___x_3535_, 1, v_k_3500_);
lean_ctor_set(v___x_3535_, 0, v___x_3543_);
v___x_3545_ = v___x_3535_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3549_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3549_, 3, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3549_, 4, v_r_3503_);
v___x_3545_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3547_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v___x_3545_);
lean_ctor_set(v___x_3523_, 3, v___y_3540_);
lean_ctor_set(v___x_3523_, 2, v_v_3527_);
lean_ctor_set(v___x_3523_, 1, v_k_3526_);
lean_ctor_set(v___x_3523_, 0, v___x_3538_);
v___x_3547_ = v___x_3523_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3538_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v___y_3540_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v___x_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
v___jp_3550_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = lean_nat_add(v___x_3537_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec(v___x_3537_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v_l_3528_);
lean_ctor_set(v___x_3507_, 3, v_tree_3510_);
lean_ctor_set(v___x_3507_, 2, v_v_3512_);
lean_ctor_set(v___x_3507_, 1, v_k_3511_);
lean_ctor_set(v___x_3507_, 0, v___x_3552_);
v___x_3554_ = v___x_3507_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_tree_3510_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_l_3528_);
v___x_3554_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3555_; 
v___x_3555_ = lean_nat_add(v___x_3504_, v_size_3530_);
if (lean_obj_tag(v_r_3529_) == 0)
{
lean_object* v_size_3556_; 
v_size_3556_ = lean_ctor_get(v_r_3529_, 0);
lean_inc(v_size_3556_);
v___y_3540_ = v___x_3554_;
v___y_3541_ = v___x_3555_;
v___y_3542_ = v_size_3556_;
goto v___jp_3539_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_unsigned_to_nat(0u);
v___y_3540_ = v___x_3554_;
v___y_3541_ = v___x_3555_;
v___y_3542_ = v___x_3557_;
goto v___jp_3539_;
}
}
}
}
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3567_ = lean_nat_add(v___x_3504_, v_size_3513_);
v___x_3568_ = lean_nat_add(v___x_3567_, v_size_3499_);
lean_dec(v_size_3499_);
v___x_3569_ = lean_nat_add(v___x_3567_, v_size_3525_);
lean_dec(v___x_3567_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_l_3502_);
lean_ctor_set(v___x_3523_, 3, v_tree_3510_);
lean_ctor_set(v___x_3523_, 2, v_v_3512_);
lean_ctor_set(v___x_3523_, 1, v_k_3511_);
lean_ctor_set(v___x_3523_, 0, v___x_3569_);
v___x_3571_ = v___x_3523_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v_tree_3510_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v_l_3502_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v_r_3503_);
lean_ctor_set(v___x_3507_, 3, v___x_3571_);
lean_ctor_set(v___x_3507_, 2, v_v_3501_);
lean_ctor_set(v___x_3507_, 1, v_k_3500_);
lean_ctor_set(v___x_3507_, 0, v___x_3568_);
v___x_3573_ = v___x_3507_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v___x_3571_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_r_3503_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
else
{
lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3635_; 
lean_inc(v_r_3503_);
lean_inc(v_v_3501_);
lean_inc(v_k_3500_);
lean_inc(v_size_3499_);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3635_ == 0)
{
lean_object* v_unused_3636_; lean_object* v_unused_3637_; lean_object* v_unused_3638_; lean_object* v_unused_3639_; lean_object* v_unused_3640_; 
v_unused_3636_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3636_);
v_unused_3637_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3637_);
v_unused_3638_ = lean_ctor_get(v_r_3315_, 2);
lean_dec(v_unused_3638_);
v_unused_3639_ = lean_ctor_get(v_r_3315_, 1);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3640_);
v___x_3583_ = v_r_3315_;
v_isShared_3584_ = v_isSharedCheck_3635_;
goto v_resetjp_3582_;
}
else
{
lean_dec(v_r_3315_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3635_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
if (lean_obj_tag(v_l_3502_) == 0)
{
if (lean_obj_tag(v_r_3503_) == 0)
{
lean_object* v_k_3585_; lean_object* v_v_3586_; lean_object* v_size_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
v_k_3585_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_k_3585_);
v_v_3586_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_v_3586_);
lean_dec_ref(v___x_3509_);
v_size_3587_ = lean_ctor_get(v_l_3502_, 0);
v___x_3588_ = lean_nat_add(v___x_3504_, v_size_3499_);
lean_dec(v_size_3499_);
v___x_3589_ = lean_nat_add(v___x_3504_, v_size_3587_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 4, v_l_3502_);
lean_ctor_set(v___x_3583_, 3, v_tree_3510_);
lean_ctor_set(v___x_3583_, 2, v_v_3586_);
lean_ctor_set(v___x_3583_, 1, v_k_3585_);
lean_ctor_set(v___x_3583_, 0, v___x_3589_);
v___x_3591_ = v___x_3583_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3585_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3586_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_tree_3510_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_l_3502_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v_r_3503_);
lean_ctor_set(v___x_3507_, 3, v___x_3591_);
lean_ctor_set(v___x_3507_, 2, v_v_3501_);
lean_ctor_set(v___x_3507_, 1, v_k_3500_);
lean_ctor_set(v___x_3507_, 0, v___x_3588_);
v___x_3593_ = v___x_3507_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v_r_3503_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
else
{
lean_object* v_k_3596_; lean_object* v_v_3597_; lean_object* v_k_3598_; lean_object* v_v_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_size_3499_);
v_k_3596_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_k_3596_);
v_v_3597_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_v_3597_);
lean_dec_ref(v___x_3509_);
v_k_3598_ = lean_ctor_get(v_l_3502_, 1);
v_v_3599_ = lean_ctor_get(v_l_3502_, 2);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_l_3502_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; lean_object* v_unused_3615_; lean_object* v_unused_3616_; 
v_unused_3614_ = lean_ctor_get(v_l_3502_, 4);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_l_3502_, 3);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_l_3502_, 0);
lean_dec(v_unused_3616_);
v___x_3601_ = v_l_3502_;
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_v_3599_);
lean_inc(v_k_3598_);
lean_dec(v_l_3502_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3603_ = lean_unsigned_to_nat(3u);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 4, v_r_3503_);
lean_ctor_set(v___x_3601_, 3, v_r_3503_);
lean_ctor_set(v___x_3601_, 2, v_v_3597_);
lean_ctor_set(v___x_3601_, 1, v_k_3596_);
lean_ctor_set(v___x_3601_, 0, v___x_3504_);
v___x_3605_ = v___x_3601_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3596_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_r_3503_);
v___x_3605_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 3, v_r_3503_);
lean_ctor_set(v___x_3583_, 0, v___x_3504_);
v___x_3607_ = v___x_3583_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_r_3503_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v___x_3607_);
lean_ctor_set(v___x_3507_, 3, v___x_3605_);
lean_ctor_set(v___x_3507_, 2, v_v_3599_);
lean_ctor_set(v___x_3507_, 1, v_k_3598_);
lean_ctor_set(v___x_3507_, 0, v___x_3603_);
v___x_3609_ = v___x_3507_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3598_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3599_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3503_) == 0)
{
lean_object* v_k_3617_; lean_object* v_v_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec(v_size_3499_);
v_k_3617_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_k_3617_);
v_v_3618_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_v_3618_);
lean_dec_ref(v___x_3509_);
v___x_3619_ = lean_unsigned_to_nat(3u);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 4, v_l_3502_);
lean_ctor_set(v___x_3583_, 2, v_v_3618_);
lean_ctor_set(v___x_3583_, 1, v_k_3617_);
lean_ctor_set(v___x_3583_, 0, v___x_3504_);
v___x_3621_ = v___x_3583_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3617_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3618_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_l_3502_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_l_3502_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v_r_3503_);
lean_ctor_set(v___x_3507_, 3, v___x_3621_);
lean_ctor_set(v___x_3507_, 2, v_v_3501_);
lean_ctor_set(v___x_3507_, 1, v_k_3500_);
lean_ctor_set(v___x_3507_, 0, v___x_3619_);
v___x_3623_ = v___x_3507_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_r_3503_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
else
{
lean_object* v_k_3626_; lean_object* v_v_3627_; lean_object* v___x_3629_; 
v_k_3626_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_k_3626_);
v_v_3627_ = lean_ctor_get(v___x_3509_, 1);
lean_inc(v_v_3627_);
lean_dec_ref(v___x_3509_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 3, v_r_3503_);
v___x_3629_ = v___x_3583_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_size_3499_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_r_3503_);
v___x_3629_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3630_ = lean_unsigned_to_nat(2u);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 4, v___x_3629_);
lean_ctor_set(v___x_3507_, 3, v_r_3503_);
lean_ctor_set(v___x_3507_, 2, v_v_3627_);
lean_ctor_set(v___x_3507_, 1, v_k_3626_);
lean_ctor_set(v___x_3507_, 0, v___x_3630_);
v___x_3632_ = v___x_3507_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_k_3626_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_v_3627_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v___x_3629_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
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
lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3799_; 
lean_inc(v_r_3503_);
lean_inc(v_v_3501_);
lean_inc(v_k_3500_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_r_3315_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; 
v_unused_3800_ = lean_ctor_get(v_r_3315_, 4);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_r_3315_, 3);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_r_3315_, 2);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_r_3315_, 1);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_r_3315_, 0);
lean_dec(v_unused_3804_);
v___x_3648_ = v_r_3315_;
v_isShared_3649_ = v_isSharedCheck_3799_;
goto v_resetjp_3647_;
}
else
{
lean_dec(v_r_3315_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3799_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v_tree_3651_; 
v___x_3650_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3500_, v_v_3501_, v_l_3502_, v_r_3503_);
v_tree_3651_ = lean_ctor_get(v___x_3650_, 2);
lean_inc(v_tree_3651_);
if (lean_obj_tag(v_tree_3651_) == 0)
{
lean_object* v_k_3652_; lean_object* v_v_3653_; lean_object* v_size_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_k_3652_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_k_3652_);
v_v_3653_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_v_3653_);
lean_dec_ref(v___x_3650_);
v_size_3654_ = lean_ctor_get(v_tree_3651_, 0);
v___x_3655_ = lean_unsigned_to_nat(3u);
v___x_3656_ = lean_nat_mul(v___x_3655_, v_size_3654_);
v___x_3657_ = lean_nat_dec_lt(v___x_3656_, v_size_3494_);
lean_dec(v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
lean_dec(v_r_3498_);
v___x_3658_ = lean_nat_add(v___x_3504_, v_size_3494_);
v___x_3659_ = lean_nat_add(v___x_3658_, v_size_3654_);
lean_dec(v___x_3658_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_tree_3651_);
lean_ctor_set(v___x_3648_, 3, v_l_3314_);
lean_ctor_set(v___x_3648_, 2, v_v_3653_);
lean_ctor_set(v___x_3648_, 1, v_k_3652_);
lean_ctor_set(v___x_3648_, 0, v___x_3659_);
v___x_3661_ = v___x_3648_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_k_3652_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_v_3653_);
lean_ctor_set(v_reuseFailAlloc_3662_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3662_, 4, v_tree_3651_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
else
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3728_; 
lean_inc(v_l_3497_);
lean_inc(v_v_3496_);
lean_inc(v_k_3495_);
lean_inc(v_size_3494_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3729_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_l_3314_, 2);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_l_3314_, 1);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3733_);
v___x_3664_ = v_l_3314_;
v_isShared_3665_ = v_isSharedCheck_3728_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_l_3314_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3728_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_size_3666_; lean_object* v_size_3667_; lean_object* v_k_3668_; lean_object* v_v_3669_; lean_object* v_l_3670_; lean_object* v_r_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_size_3666_ = lean_ctor_get(v_l_3497_, 0);
v_size_3667_ = lean_ctor_get(v_r_3498_, 0);
v_k_3668_ = lean_ctor_get(v_r_3498_, 1);
v_v_3669_ = lean_ctor_get(v_r_3498_, 2);
v_l_3670_ = lean_ctor_get(v_r_3498_, 3);
v_r_3671_ = lean_ctor_get(v_r_3498_, 4);
v___x_3672_ = lean_unsigned_to_nat(2u);
v___x_3673_ = lean_nat_mul(v___x_3672_, v_size_3666_);
v___x_3674_ = lean_nat_dec_lt(v_size_3667_, v___x_3673_);
lean_dec(v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3712_; 
lean_inc(v_r_3671_);
lean_inc(v_l_3670_);
lean_inc(v_v_3669_);
lean_inc(v_k_3668_);
lean_del_object(v___x_3664_);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_r_3498_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; 
v_unused_3713_ = lean_ctor_get(v_r_3498_, 4);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_r_3498_, 3);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_r_3498_, 2);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_r_3498_, 1);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_r_3498_, 0);
lean_dec(v_unused_3717_);
v___x_3676_ = v_r_3498_;
v_isShared_3677_ = v_isSharedCheck_3712_;
goto v_resetjp_3675_;
}
else
{
lean_dec(v_r_3498_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3712_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___x_3700_; lean_object* v___y_3702_; 
v___x_3678_ = lean_nat_add(v___x_3504_, v_size_3494_);
lean_dec(v_size_3494_);
v___x_3679_ = lean_nat_add(v___x_3678_, v_size_3654_);
lean_dec(v___x_3678_);
v___x_3700_ = lean_nat_add(v___x_3504_, v_size_3666_);
if (lean_obj_tag(v_l_3670_) == 0)
{
lean_object* v_size_3710_; 
v_size_3710_ = lean_ctor_get(v_l_3670_, 0);
lean_inc(v_size_3710_);
v___y_3702_ = v_size_3710_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_unsigned_to_nat(0u);
v___y_3702_ = v___x_3711_;
goto v___jp_3701_;
}
v___jp_3680_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_nat_add(v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec(v___y_3682_);
lean_inc_ref(v_tree_3651_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 4, v_tree_3651_);
lean_ctor_set(v___x_3676_, 3, v_r_3671_);
lean_ctor_set(v___x_3676_, 2, v_v_3653_);
lean_ctor_set(v___x_3676_, 1, v_k_3652_);
lean_ctor_set(v___x_3676_, 0, v___x_3684_);
v___x_3686_ = v___x_3676_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_k_3652_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_v_3653_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v_r_3671_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_tree_3651_);
v___x_3686_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
v_isSharedCheck_3693_ = !lean_is_exclusive(v_tree_3651_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; lean_object* v_unused_3698_; 
v_unused_3694_ = lean_ctor_get(v_tree_3651_, 4);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_tree_3651_, 3);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_tree_3651_, 2);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_tree_3651_, 1);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_tree_3651_, 0);
lean_dec(v_unused_3698_);
v___x_3688_ = v_tree_3651_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_dec(v_tree_3651_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 4, v___x_3686_);
lean_ctor_set(v___x_3688_, 3, v___y_3681_);
lean_ctor_set(v___x_3688_, 2, v_v_3669_);
lean_ctor_set(v___x_3688_, 1, v_k_3668_);
lean_ctor_set(v___x_3688_, 0, v___x_3679_);
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v___y_3681_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v___x_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
v___jp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_nat_add(v___x_3700_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec(v___x_3700_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_l_3670_);
lean_ctor_set(v___x_3648_, 3, v_l_3497_);
lean_ctor_set(v___x_3648_, 2, v_v_3496_);
lean_ctor_set(v___x_3648_, 1, v_k_3495_);
lean_ctor_set(v___x_3648_, 0, v___x_3703_);
v___x_3705_ = v___x_3648_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_k_3495_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_v_3496_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3709_, 4, v_l_3670_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_nat_add(v___x_3504_, v_size_3654_);
if (lean_obj_tag(v_r_3671_) == 0)
{
lean_object* v_size_3707_; 
v_size_3707_ = lean_ctor_get(v_r_3671_, 0);
lean_inc(v_size_3707_);
v___y_3681_ = v___x_3705_;
v___y_3682_ = v___x_3706_;
v___y_3683_ = v_size_3707_;
goto v___jp_3680_;
}
else
{
lean_object* v___x_3708_; 
v___x_3708_ = lean_unsigned_to_nat(0u);
v___y_3681_ = v___x_3705_;
v___y_3682_ = v___x_3706_;
v___y_3683_ = v___x_3708_;
goto v___jp_3680_;
}
}
}
}
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3718_ = lean_nat_add(v___x_3504_, v_size_3494_);
lean_dec(v_size_3494_);
v___x_3719_ = lean_nat_add(v___x_3718_, v_size_3654_);
lean_dec(v___x_3718_);
v___x_3720_ = lean_nat_add(v___x_3504_, v_size_3654_);
v___x_3721_ = lean_nat_add(v___x_3720_, v_size_3667_);
lean_dec(v___x_3720_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_tree_3651_);
lean_ctor_set(v___x_3648_, 3, v_r_3498_);
lean_ctor_set(v___x_3648_, 2, v_v_3653_);
lean_ctor_set(v___x_3648_, 1, v_k_3652_);
lean_ctor_set(v___x_3648_, 0, v___x_3721_);
v___x_3723_ = v___x_3648_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3652_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3653_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_r_3498_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_tree_3651_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v___x_3723_);
lean_ctor_set(v___x_3664_, 0, v___x_3719_);
v___x_3725_ = v___x_3664_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_k_3495_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_v_3496_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3497_) == 0)
{
lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3757_; 
lean_inc_ref(v_l_3497_);
lean_inc(v_v_3496_);
lean_inc(v_k_3495_);
lean_inc(v_size_3494_);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; 
v_unused_3758_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_l_3314_, 2);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_l_3314_, 1);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3762_);
v___x_3735_ = v_l_3314_;
v_isShared_3736_ = v_isSharedCheck_3757_;
goto v_resetjp_3734_;
}
else
{
lean_dec(v_l_3314_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3757_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
if (lean_obj_tag(v_r_3498_) == 0)
{
lean_object* v_k_3737_; lean_object* v_v_3738_; lean_object* v_size_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v_k_3737_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_k_3737_);
v_v_3738_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_v_3738_);
lean_dec_ref(v___x_3650_);
v_size_3739_ = lean_ctor_get(v_r_3498_, 0);
v___x_3740_ = lean_nat_add(v___x_3504_, v_size_3494_);
lean_dec(v_size_3494_);
v___x_3741_ = lean_nat_add(v___x_3504_, v_size_3739_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_tree_3651_);
lean_ctor_set(v___x_3648_, 3, v_r_3498_);
lean_ctor_set(v___x_3648_, 2, v_v_3738_);
lean_ctor_set(v___x_3648_, 1, v_k_3737_);
lean_ctor_set(v___x_3648_, 0, v___x_3741_);
v___x_3743_ = v___x_3648_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3747_, 1, v_k_3737_);
lean_ctor_set(v_reuseFailAlloc_3747_, 2, v_v_3738_);
lean_ctor_set(v_reuseFailAlloc_3747_, 3, v_r_3498_);
lean_ctor_set(v_reuseFailAlloc_3747_, 4, v_tree_3651_);
v___x_3743_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3745_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v___x_3743_);
lean_ctor_set(v___x_3735_, 0, v___x_3740_);
v___x_3745_ = v___x_3735_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_k_3495_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_v_3496_);
lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3746_, 4, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
else
{
lean_object* v_k_3748_; lean_object* v_v_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
lean_dec(v_size_3494_);
v_k_3748_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_k_3748_);
v_v_3749_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_v_3749_);
lean_dec_ref(v___x_3650_);
v___x_3750_ = lean_unsigned_to_nat(3u);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_r_3498_);
lean_ctor_set(v___x_3648_, 3, v_r_3498_);
lean_ctor_set(v___x_3648_, 2, v_v_3749_);
lean_ctor_set(v___x_3648_, 1, v_k_3748_);
lean_ctor_set(v___x_3648_, 0, v___x_3504_);
v___x_3752_ = v___x_3648_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_r_3498_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_r_3498_);
v___x_3752_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3754_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v___x_3752_);
lean_ctor_set(v___x_3735_, 0, v___x_3750_);
v___x_3754_ = v___x_3735_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3495_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3496_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v___x_3752_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3498_) == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3787_; 
lean_inc(v_l_3497_);
lean_inc(v_v_3496_);
lean_inc(v_k_3495_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; lean_object* v_unused_3789_; lean_object* v_unused_3790_; lean_object* v_unused_3791_; lean_object* v_unused_3792_; 
v_unused_3788_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_l_3314_, 2);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_l_3314_, 1);
lean_dec(v_unused_3791_);
v_unused_3792_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3792_);
v___x_3764_ = v_l_3314_;
v_isShared_3765_ = v_isSharedCheck_3787_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v_l_3314_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3787_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v_k_3768_; lean_object* v_v_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3783_; 
v_k_3766_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_k_3766_);
v_v_3767_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_v_3767_);
lean_dec_ref(v___x_3650_);
v_k_3768_ = lean_ctor_get(v_r_3498_, 1);
v_v_3769_ = lean_ctor_get(v_r_3498_, 2);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_r_3498_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; 
v_unused_3784_ = lean_ctor_get(v_r_3498_, 4);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_r_3498_, 3);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_r_3498_, 0);
lean_dec(v_unused_3786_);
v___x_3771_ = v_r_3498_;
v_isShared_3772_ = v_isSharedCheck_3783_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_v_3769_);
lean_inc(v_k_3768_);
lean_dec(v_r_3498_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3783_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; lean_object* v___x_3775_; 
v___x_3773_ = lean_unsigned_to_nat(3u);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 4, v_l_3497_);
lean_ctor_set(v___x_3771_, 3, v_l_3497_);
lean_ctor_set(v___x_3771_, 2, v_v_3496_);
lean_ctor_set(v___x_3771_, 1, v_k_3495_);
lean_ctor_set(v___x_3771_, 0, v___x_3504_);
v___x_3775_ = v___x_3771_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3495_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3496_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_l_3497_);
v___x_3775_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_l_3497_);
lean_ctor_set(v___x_3648_, 3, v_l_3497_);
lean_ctor_set(v___x_3648_, 2, v_v_3767_);
lean_ctor_set(v___x_3648_, 1, v_k_3766_);
lean_ctor_set(v___x_3648_, 0, v___x_3504_);
v___x_3777_ = v___x_3648_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3766_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3767_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_l_3497_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_l_3497_);
v___x_3777_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
lean_object* v___x_3779_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 4, v___x_3777_);
lean_ctor_set(v___x_3764_, 3, v___x_3775_);
lean_ctor_set(v___x_3764_, 2, v_v_3769_);
lean_ctor_set(v___x_3764_, 1, v_k_3768_);
lean_ctor_set(v___x_3764_, 0, v___x_3773_);
v___x_3779_ = v___x_3764_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3773_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3768_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3769_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v___x_3777_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
}
else
{
lean_object* v_k_3793_; lean_object* v_v_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v_k_3793_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_k_3793_);
v_v_3794_ = lean_ctor_get(v___x_3650_, 1);
lean_inc(v_v_3794_);
lean_dec_ref(v___x_3650_);
v___x_3795_ = lean_unsigned_to_nat(2u);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 4, v_r_3498_);
lean_ctor_set(v___x_3648_, 3, v_l_3314_);
lean_ctor_set(v___x_3648_, 2, v_v_3794_);
lean_ctor_set(v___x_3648_, 1, v_k_3793_);
lean_ctor_set(v___x_3648_, 0, v___x_3795_);
v___x_3797_ = v___x_3648_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3793_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3794_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_r_3498_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
}
else
{
return v_l_3314_;
}
}
else
{
return v_r_3315_;
}
}
default: 
{
lean_object* v_impl_3805_; lean_object* v___x_3806_; 
v_impl_3805_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3310_, v_r_3315_);
v___x_3806_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3805_) == 0)
{
if (lean_obj_tag(v_l_3314_) == 0)
{
lean_object* v_size_3807_; lean_object* v_size_3808_; lean_object* v_k_3809_; lean_object* v_v_3810_; lean_object* v_l_3811_; lean_object* v_r_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_size_3807_ = lean_ctor_get(v_impl_3805_, 0);
lean_inc(v_size_3807_);
v_size_3808_ = lean_ctor_get(v_l_3314_, 0);
v_k_3809_ = lean_ctor_get(v_l_3314_, 1);
v_v_3810_ = lean_ctor_get(v_l_3314_, 2);
v_l_3811_ = lean_ctor_get(v_l_3314_, 3);
v_r_3812_ = lean_ctor_get(v_l_3314_, 4);
lean_inc(v_r_3812_);
v___x_3813_ = lean_unsigned_to_nat(3u);
v___x_3814_ = lean_nat_mul(v___x_3813_, v_size_3807_);
v___x_3815_ = lean_nat_dec_lt(v___x_3814_, v_size_3808_);
lean_dec(v___x_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3819_; 
lean_dec(v_r_3812_);
v___x_3816_ = lean_nat_add(v___x_3806_, v_size_3808_);
v___x_3817_ = lean_nat_add(v___x_3816_, v_size_3807_);
lean_dec(v_size_3807_);
lean_dec(v___x_3816_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_impl_3805_);
lean_ctor_set(v___x_3317_, 0, v___x_3817_);
v___x_3819_ = v___x_3317_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3820_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3820_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3820_, 4, v_impl_3805_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
else
{
lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3886_; 
lean_inc(v_l_3811_);
lean_inc(v_v_3810_);
lean_inc(v_k_3809_);
lean_inc(v_size_3808_);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3886_ == 0)
{
lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; 
v_unused_3887_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3314_, 2);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_l_3314_, 1);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3891_);
v___x_3822_ = v_l_3314_;
v_isShared_3823_ = v_isSharedCheck_3886_;
goto v_resetjp_3821_;
}
else
{
lean_dec(v_l_3314_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3886_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v_size_3824_; lean_object* v_size_3825_; lean_object* v_k_3826_; lean_object* v_v_3827_; lean_object* v_l_3828_; lean_object* v_r_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v_size_3824_ = lean_ctor_get(v_l_3811_, 0);
v_size_3825_ = lean_ctor_get(v_r_3812_, 0);
v_k_3826_ = lean_ctor_get(v_r_3812_, 1);
v_v_3827_ = lean_ctor_get(v_r_3812_, 2);
v_l_3828_ = lean_ctor_get(v_r_3812_, 3);
v_r_3829_ = lean_ctor_get(v_r_3812_, 4);
v___x_3830_ = lean_unsigned_to_nat(2u);
v___x_3831_ = lean_nat_mul(v___x_3830_, v_size_3824_);
v___x_3832_ = lean_nat_dec_lt(v_size_3825_, v___x_3831_);
lean_dec(v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3861_; 
lean_inc(v_r_3829_);
lean_inc(v_l_3828_);
lean_inc(v_v_3827_);
lean_inc(v_k_3826_);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_r_3812_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; lean_object* v_unused_3863_; lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; 
v_unused_3862_ = lean_ctor_get(v_r_3812_, 4);
lean_dec(v_unused_3862_);
v_unused_3863_ = lean_ctor_get(v_r_3812_, 3);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_r_3812_, 2);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_r_3812_, 1);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_r_3812_, 0);
lean_dec(v_unused_3866_);
v___x_3834_ = v_r_3812_;
v_isShared_3835_ = v_isSharedCheck_3861_;
goto v_resetjp_3833_;
}
else
{
lean_dec(v_r_3812_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3861_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___x_3849_; lean_object* v___y_3851_; 
v___x_3836_ = lean_nat_add(v___x_3806_, v_size_3808_);
lean_dec(v_size_3808_);
v___x_3837_ = lean_nat_add(v___x_3836_, v_size_3807_);
lean_dec(v___x_3836_);
v___x_3849_ = lean_nat_add(v___x_3806_, v_size_3824_);
if (lean_obj_tag(v_l_3828_) == 0)
{
lean_object* v_size_3859_; 
v_size_3859_ = lean_ctor_get(v_l_3828_, 0);
lean_inc(v_size_3859_);
v___y_3851_ = v_size_3859_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_unsigned_to_nat(0u);
v___y_3851_ = v___x_3860_;
goto v___jp_3850_;
}
v___jp_3838_:
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
v___x_3842_ = lean_nat_add(v___y_3839_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec(v___y_3839_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 4, v_impl_3805_);
lean_ctor_set(v___x_3834_, 3, v_r_3829_);
lean_ctor_set(v___x_3834_, 2, v_v_3313_);
lean_ctor_set(v___x_3834_, 1, v_k_3312_);
lean_ctor_set(v___x_3834_, 0, v___x_3842_);
v___x_3844_ = v___x_3834_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3842_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_r_3829_);
lean_ctor_set(v_reuseFailAlloc_3848_, 4, v_impl_3805_);
v___x_3844_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3846_; 
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 4, v___x_3844_);
lean_ctor_set(v___x_3822_, 3, v___y_3840_);
lean_ctor_set(v___x_3822_, 2, v_v_3827_);
lean_ctor_set(v___x_3822_, 1, v_k_3826_);
lean_ctor_set(v___x_3822_, 0, v___x_3837_);
v___x_3846_ = v___x_3822_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3837_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_k_3826_);
lean_ctor_set(v_reuseFailAlloc_3847_, 2, v_v_3827_);
lean_ctor_set(v_reuseFailAlloc_3847_, 3, v___y_3840_);
lean_ctor_set(v_reuseFailAlloc_3847_, 4, v___x_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
v___jp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_nat_add(v___x_3849_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec(v___x_3849_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_l_3828_);
lean_ctor_set(v___x_3317_, 3, v_l_3811_);
lean_ctor_set(v___x_3317_, 2, v_v_3810_);
lean_ctor_set(v___x_3317_, 1, v_k_3809_);
lean_ctor_set(v___x_3317_, 0, v___x_3852_);
v___x_3854_ = v___x_3317_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_k_3809_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_v_3810_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_l_3811_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_l_3828_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_nat_add(v___x_3806_, v_size_3807_);
lean_dec(v_size_3807_);
if (lean_obj_tag(v_r_3829_) == 0)
{
lean_object* v_size_3856_; 
v_size_3856_ = lean_ctor_get(v_r_3829_, 0);
lean_inc(v_size_3856_);
v___y_3839_ = v___x_3855_;
v___y_3840_ = v___x_3854_;
v___y_3841_ = v_size_3856_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_unsigned_to_nat(0u);
v___y_3839_ = v___x_3855_;
v___y_3840_ = v___x_3854_;
v___y_3841_ = v___x_3857_;
goto v___jp_3838_;
}
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_del_object(v___x_3317_);
v___x_3867_ = lean_nat_add(v___x_3806_, v_size_3808_);
lean_dec(v_size_3808_);
v___x_3868_ = lean_nat_add(v___x_3867_, v_size_3807_);
lean_dec(v___x_3867_);
v___x_3869_ = lean_nat_add(v___x_3806_, v_size_3807_);
lean_dec(v_size_3807_);
v___x_3870_ = lean_nat_add(v___x_3869_, v_size_3825_);
lean_dec(v___x_3869_);
lean_inc_ref(v_impl_3805_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 4, v_impl_3805_);
lean_ctor_set(v___x_3822_, 3, v_r_3812_);
lean_ctor_set(v___x_3822_, 2, v_v_3313_);
lean_ctor_set(v___x_3822_, 1, v_k_3312_);
lean_ctor_set(v___x_3822_, 0, v___x_3870_);
v___x_3872_ = v___x_3822_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3885_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3885_, 3, v_r_3812_);
lean_ctor_set(v_reuseFailAlloc_3885_, 4, v_impl_3805_);
v___x_3872_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3879_; 
v_isSharedCheck_3879_ = !lean_is_exclusive(v_impl_3805_);
if (v_isSharedCheck_3879_ == 0)
{
lean_object* v_unused_3880_; lean_object* v_unused_3881_; lean_object* v_unused_3882_; lean_object* v_unused_3883_; lean_object* v_unused_3884_; 
v_unused_3880_ = lean_ctor_get(v_impl_3805_, 4);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_impl_3805_, 3);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_impl_3805_, 2);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_impl_3805_, 1);
lean_dec(v_unused_3883_);
v_unused_3884_ = lean_ctor_get(v_impl_3805_, 0);
lean_dec(v_unused_3884_);
v___x_3874_ = v_impl_3805_;
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
else
{
lean_dec(v_impl_3805_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3879_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3877_; 
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 4, v___x_3872_);
lean_ctor_set(v___x_3874_, 3, v_l_3811_);
lean_ctor_set(v___x_3874_, 2, v_v_3810_);
lean_ctor_set(v___x_3874_, 1, v_k_3809_);
lean_ctor_set(v___x_3874_, 0, v___x_3868_);
v___x_3877_ = v___x_3874_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3878_, 1, v_k_3809_);
lean_ctor_set(v_reuseFailAlloc_3878_, 2, v_v_3810_);
lean_ctor_set(v_reuseFailAlloc_3878_, 3, v_l_3811_);
lean_ctor_set(v_reuseFailAlloc_3878_, 4, v___x_3872_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v_size_3892_ = lean_ctor_get(v_impl_3805_, 0);
lean_inc(v_size_3892_);
v___x_3893_ = lean_nat_add(v___x_3806_, v_size_3892_);
lean_dec(v_size_3892_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_impl_3805_);
lean_ctor_set(v___x_3317_, 0, v___x_3893_);
v___x_3895_ = v___x_3317_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3896_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3896_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3896_, 4, v_impl_3805_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
else
{
if (lean_obj_tag(v_l_3314_) == 0)
{
lean_object* v_l_3897_; 
v_l_3897_ = lean_ctor_get(v_l_3314_, 3);
if (lean_obj_tag(v_l_3897_) == 0)
{
lean_object* v_r_3898_; 
lean_inc_ref(v_l_3897_);
v_r_3898_ = lean_ctor_get(v_l_3314_, 4);
lean_inc(v_r_3898_);
if (lean_obj_tag(v_r_3898_) == 0)
{
lean_object* v_size_3899_; lean_object* v_k_3900_; lean_object* v_v_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3914_; 
v_size_3899_ = lean_ctor_get(v_l_3314_, 0);
v_k_3900_ = lean_ctor_get(v_l_3314_, 1);
v_v_3901_ = lean_ctor_get(v_l_3314_, 2);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3915_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3916_);
v___x_3903_ = v_l_3314_;
v_isShared_3904_ = v_isSharedCheck_3914_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_v_3901_);
lean_inc(v_k_3900_);
lean_inc(v_size_3899_);
lean_dec(v_l_3314_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3914_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v_size_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v_size_3905_ = lean_ctor_get(v_r_3898_, 0);
v___x_3906_ = lean_nat_add(v___x_3806_, v_size_3899_);
lean_dec(v_size_3899_);
v___x_3907_ = lean_nat_add(v___x_3806_, v_size_3905_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 4, v_impl_3805_);
lean_ctor_set(v___x_3903_, 3, v_r_3898_);
lean_ctor_set(v___x_3903_, 2, v_v_3313_);
lean_ctor_set(v___x_3903_, 1, v_k_3312_);
lean_ctor_set(v___x_3903_, 0, v___x_3907_);
v___x_3909_ = v___x_3903_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3913_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3913_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3913_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3913_, 4, v_impl_3805_);
v___x_3909_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3911_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v___x_3909_);
lean_ctor_set(v___x_3317_, 3, v_l_3897_);
lean_ctor_set(v___x_3317_, 2, v_v_3901_);
lean_ctor_set(v___x_3317_, 1, v_k_3900_);
lean_ctor_set(v___x_3317_, 0, v___x_3906_);
v___x_3911_ = v___x_3317_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_k_3900_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_v_3901_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_k_3917_; lean_object* v_v_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3929_; 
v_k_3917_ = lean_ctor_get(v_l_3314_, 1);
v_v_3918_ = lean_ctor_get(v_l_3314_, 2);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3930_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3932_);
v___x_3920_ = v_l_3314_;
v_isShared_3921_ = v_isSharedCheck_3929_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_v_3918_);
lean_inc(v_k_3917_);
lean_dec(v_l_3314_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3929_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3922_ = lean_unsigned_to_nat(3u);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 3, v_r_3898_);
lean_ctor_set(v___x_3920_, 2, v_v_3313_);
lean_ctor_set(v___x_3920_, 1, v_k_3312_);
lean_ctor_set(v___x_3920_, 0, v___x_3806_);
v___x_3924_ = v___x_3920_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3928_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3928_, 4, v_r_3898_);
v___x_3924_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3926_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v___x_3924_);
lean_ctor_set(v___x_3317_, 3, v_l_3897_);
lean_ctor_set(v___x_3317_, 2, v_v_3918_);
lean_ctor_set(v___x_3317_, 1, v_k_3917_);
lean_ctor_set(v___x_3317_, 0, v___x_3922_);
v___x_3926_ = v___x_3317_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3917_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3918_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
else
{
lean_object* v_r_3933_; 
v_r_3933_ = lean_ctor_get(v_l_3314_, 4);
lean_inc(v_r_3933_);
if (lean_obj_tag(v_r_3933_) == 0)
{
lean_object* v_k_3934_; lean_object* v_v_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3958_; 
lean_inc(v_l_3897_);
v_k_3934_ = lean_ctor_get(v_l_3314_, 1);
v_v_3935_ = lean_ctor_get(v_l_3314_, 2);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3958_ == 0)
{
lean_object* v_unused_3959_; lean_object* v_unused_3960_; lean_object* v_unused_3961_; 
v_unused_3959_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3959_);
v_unused_3960_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3960_);
v_unused_3961_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3961_);
v___x_3937_ = v_l_3314_;
v_isShared_3938_ = v_isSharedCheck_3958_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_v_3935_);
lean_inc(v_k_3934_);
lean_dec(v_l_3314_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3958_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v_k_3939_; lean_object* v_v_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3954_; 
v_k_3939_ = lean_ctor_get(v_r_3933_, 1);
v_v_3940_ = lean_ctor_get(v_r_3933_, 2);
v_isSharedCheck_3954_ = !lean_is_exclusive(v_r_3933_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; lean_object* v_unused_3956_; lean_object* v_unused_3957_; 
v_unused_3955_ = lean_ctor_get(v_r_3933_, 4);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_r_3933_, 3);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_r_3933_, 0);
lean_dec(v_unused_3957_);
v___x_3942_ = v_r_3933_;
v_isShared_3943_ = v_isSharedCheck_3954_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_v_3940_);
lean_inc(v_k_3939_);
lean_dec(v_r_3933_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3954_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3944_ = lean_unsigned_to_nat(3u);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 4, v_l_3897_);
lean_ctor_set(v___x_3942_, 3, v_l_3897_);
lean_ctor_set(v___x_3942_, 2, v_v_3935_);
lean_ctor_set(v___x_3942_, 1, v_k_3934_);
lean_ctor_set(v___x_3942_, 0, v___x_3806_);
v___x_3946_ = v___x_3942_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_k_3934_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_v_3935_);
lean_ctor_set(v_reuseFailAlloc_3953_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3953_, 4, v_l_3897_);
v___x_3946_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
lean_object* v___x_3948_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 4, v_l_3897_);
lean_ctor_set(v___x_3937_, 2, v_v_3313_);
lean_ctor_set(v___x_3937_, 1, v_k_3312_);
lean_ctor_set(v___x_3937_, 0, v___x_3806_);
v___x_3948_ = v___x_3937_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3952_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3952_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3952_, 4, v_l_3897_);
v___x_3948_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3950_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v___x_3948_);
lean_ctor_set(v___x_3317_, 3, v___x_3946_);
lean_ctor_set(v___x_3317_, 2, v_v_3940_);
lean_ctor_set(v___x_3317_, 1, v_k_3939_);
lean_ctor_set(v___x_3317_, 0, v___x_3944_);
v___x_3950_ = v___x_3317_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_k_3939_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v_v_3940_);
lean_ctor_set(v_reuseFailAlloc_3951_, 3, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3951_, 4, v___x_3948_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = lean_unsigned_to_nat(2u);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_r_3933_);
lean_ctor_set(v___x_3317_, 0, v___x_3962_);
v___x_3964_ = v___x_3317_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_r_3933_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_object* v___x_3967_; 
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 4, v_l_3314_);
lean_ctor_set(v___x_3317_, 0, v___x_3806_);
v___x_3967_ = v___x_3317_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_l_3314_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
}
}
else
{
return v_t_3311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3971_, lean_object* v_t_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3971_, v_t_3972_);
lean_dec(v_k_3971_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3974_, lean_object* v_x_3975_){
_start:
{
lean_object* v___x_3976_; 
v___x_3976_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3974_, v_x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3977_, lean_object* v_x_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3977_, v_x_3978_);
lean_dec(v_declName_3977_);
return v_res_3979_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3982_ = l_Lean_stringToMessageData(v___x_3981_);
return v___x_3982_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v_env_3992_; lean_object* v___f_3993_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___x_4037_; 
v___x_3991_ = lean_st_ref_get(v___y_3989_);
v_env_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_ref(v_env_3992_);
lean_dec(v___x_3991_);
lean_inc(v_declName_3983_);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3993_, 0, v_declName_3983_);
v___x_4037_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3992_, v_declName_3983_);
lean_dec_ref(v_env_3992_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_dec(v_declName_3983_);
v___y_3995_ = v___y_3987_;
v___y_3996_ = v___y_3989_;
goto v___jp_3994_;
}
else
{
uint8_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
lean_dec_ref_known(v___x_4037_, 1);
lean_dec_ref(v___f_3993_);
v___x_4038_ = 0;
v___x_4039_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4040_ = l_Lean_MessageData_ofConstName(v_declName_3983_, v___x_4038_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4039_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4041_);
lean_ctor_set(v___x_4043_, 1, v___x_4042_);
v___x_4044_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4043_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
return v___x_4044_;
}
v___jp_3994_:
{
lean_object* v___x_3997_; lean_object* v_env_3998_; lean_object* v_nextMacroScope_3999_; lean_object* v_ngen_4000_; lean_object* v_auxDeclNGen_4001_; lean_object* v_traceState_4002_; lean_object* v_messages_4003_; lean_object* v_infoState_4004_; lean_object* v_snapshotTasks_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4035_; 
v___x_3997_ = lean_st_ref_take(v___y_3996_);
v_env_3998_ = lean_ctor_get(v___x_3997_, 0);
v_nextMacroScope_3999_ = lean_ctor_get(v___x_3997_, 1);
v_ngen_4000_ = lean_ctor_get(v___x_3997_, 2);
v_auxDeclNGen_4001_ = lean_ctor_get(v___x_3997_, 3);
v_traceState_4002_ = lean_ctor_get(v___x_3997_, 4);
v_messages_4003_ = lean_ctor_get(v___x_3997_, 6);
v_infoState_4004_ = lean_ctor_get(v___x_3997_, 7);
v_snapshotTasks_4005_ = lean_ctor_get(v___x_3997_, 8);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4035_ == 0)
{
lean_object* v_unused_4036_; 
v_unused_4036_ = lean_ctor_get(v___x_3997_, 5);
lean_dec(v_unused_4036_);
v___x_4007_ = v___x_3997_;
v_isShared_4008_ = v_isSharedCheck_4035_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_snapshotTasks_4005_);
lean_inc(v_infoState_4004_);
lean_inc(v_messages_4003_);
lean_inc(v_traceState_4002_);
lean_inc(v_auxDeclNGen_4001_);
lean_inc(v_ngen_4000_);
lean_inc(v_nextMacroScope_3999_);
lean_inc(v_env_3998_);
lean_dec(v___x_3997_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4035_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4009_ = l_Lean_docStringExt;
v___x_4010_ = lean_box(2);
v___x_4011_ = lean_box(0);
v___x_4012_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4009_, v_env_3998_, v___f_3993_, v___x_4010_, v___x_4011_);
v___x_4013_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 5, v___x_4013_);
lean_ctor_set(v___x_4007_, 0, v___x_4012_);
v___x_4015_ = v___x_4007_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v_nextMacroScope_3999_);
lean_ctor_set(v_reuseFailAlloc_4034_, 2, v_ngen_4000_);
lean_ctor_set(v_reuseFailAlloc_4034_, 3, v_auxDeclNGen_4001_);
lean_ctor_set(v_reuseFailAlloc_4034_, 4, v_traceState_4002_);
lean_ctor_set(v_reuseFailAlloc_4034_, 5, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4034_, 6, v_messages_4003_);
lean_ctor_set(v_reuseFailAlloc_4034_, 7, v_infoState_4004_);
lean_ctor_set(v_reuseFailAlloc_4034_, 8, v_snapshotTasks_4005_);
v___x_4015_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v_mctx_4018_; lean_object* v_zetaDeltaFVarIds_4019_; lean_object* v_postponed_4020_; lean_object* v_diag_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4032_; 
v___x_4016_ = lean_st_ref_set(v___y_3996_, v___x_4015_);
v___x_4017_ = lean_st_ref_take(v___y_3995_);
v_mctx_4018_ = lean_ctor_get(v___x_4017_, 0);
v_zetaDeltaFVarIds_4019_ = lean_ctor_get(v___x_4017_, 2);
v_postponed_4020_ = lean_ctor_get(v___x_4017_, 3);
v_diag_4021_ = lean_ctor_get(v___x_4017_, 4);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v___x_4017_, 1);
lean_dec(v_unused_4033_);
v___x_4023_ = v___x_4017_;
v_isShared_4024_ = v_isSharedCheck_4032_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_diag_4021_);
lean_inc(v_postponed_4020_);
lean_inc(v_zetaDeltaFVarIds_4019_);
lean_inc(v_mctx_4018_);
lean_dec(v___x_4017_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4032_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4025_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_mctx_4018_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4031_, 2, v_zetaDeltaFVarIds_4019_);
lean_ctor_set(v_reuseFailAlloc_4031_, 3, v_postponed_4020_);
lean_ctor_set(v_reuseFailAlloc_4031_, 4, v_diag_4021_);
v___x_4027_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = lean_st_ref_set(v___y_3995_, v___x_4027_);
v___x_4029_ = lean_box(0);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
return v_res_4053_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4056_ = l_Lean_stringToMessageData(v___x_4055_);
return v___x_4056_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4059_ = l_Lean_stringToMessageData(v___x_4058_);
return v___x_4059_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4062_ = l_Lean_stringToMessageData(v___x_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4065_ = l_Lean_stringToMessageData(v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v___x_4074_; lean_object* v_env_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; 
v___x_4074_ = lean_st_ref_get(v_a_4072_);
v_env_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc_ref(v_env_4075_);
lean_dec(v___x_4074_);
v___x_4076_ = 1;
lean_inc(v_declName_4066_);
v___x_4077_ = l_Lean_findInternalDocString_x3f(v_env_4075_, v_declName_4066_, v___x_4076_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
if (lean_obj_tag(v_a_4078_) == 1)
{
lean_object* v_val_4079_; 
v_val_4079_ = lean_ctor_get(v_a_4078_, 0);
lean_inc(v_val_4079_);
lean_dec_ref_known(v_a_4078_, 1);
if (lean_obj_tag(v_val_4079_) == 0)
{
lean_object* v_val_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4102_; 
v_val_4080_ = lean_ctor_get(v_val_4079_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v_val_4079_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4082_ = v_val_4079_;
v_isShared_4083_ = v_isSharedCheck_4102_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_val_4080_);
lean_dec(v_val_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4102_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_removeBuiltinDocString(v_declName_4066_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4085_; 
lean_dec_ref_known(v___x_4084_, 1);
lean_del_object(v___x_4082_);
lean_inc(v_declName_4066_);
v___x_4085_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v___x_4086_; 
lean_dec_ref_known(v___x_4085_, 1);
v___x_4086_ = l_Lean_addVersoDocStringFromString(v_declName_4066_, v_val_4080_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
return v___x_4086_;
}
else
{
lean_dec(v_val_4080_);
lean_dec(v_declName_4066_);
return v___x_4085_;
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_val_4080_);
lean_dec(v_declName_4066_);
v_a_4087_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4089_ = v___x_4084_;
v_isShared_4090_ = v_isSharedCheck_4101_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4084_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4101_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v_ref_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v_ref_4091_ = lean_ctor_get(v_a_4071_, 5);
v___x_4092_ = lean_io_error_to_string(v_a_4087_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 3);
lean_ctor_set(v___x_4082_, 0, v___x_4092_);
v___x_4094_ = v___x_4082_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4098_; 
v___x_4095_ = l_Lean_MessageData_ofFormat(v___x_4094_);
lean_inc(v_ref_4091_);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v_ref_4091_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4096_);
v___x_4098_ = v___x_4089_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
else
{
lean_object* v___x_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
lean_dec(v_val_4079_);
v___x_4103_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4104_ = 0;
v___x_4105_ = l_Lean_MessageData_ofConstName(v_declName_4066_, v___x_4104_);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4103_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4108_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
return v___x_4109_;
}
}
else
{
lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
lean_dec(v_a_4078_);
v___x_4110_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4111_ = 0;
v___x_4112_ = l_Lean_MessageData_ofConstName(v_declName_4066_, v___x_4111_);
v___x_4113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4110_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4113_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4115_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
return v___x_4116_;
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_declName_4066_);
v_a_4117_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4119_ = v___x_4077_;
v_isShared_4120_ = v_isSharedCheck_4129_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4077_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4129_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v_ref_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4127_; 
v_ref_4121_ = lean_ctor_get(v_a_4071_, 5);
v___x_4122_ = lean_io_error_to_string(v_a_4117_);
v___x_4123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
v___x_4124_ = l_Lean_MessageData_ofFormat(v___x_4123_);
lean_inc(v_ref_4121_);
v___x_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4125_, 0, v_ref_4121_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
if (v_isShared_4120_ == 0)
{
lean_ctor_set(v___x_4119_, 0, v___x_4125_);
v___x_4127_ = v___x_4119_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_makeDocStringVerso(v_declName_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4139_, lean_object* v_k_4140_, lean_object* v_t_4141_, lean_object* v_h_4142_){
_start:
{
lean_object* v___x_4143_; 
v___x_4143_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4140_, v_t_4141_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4144_, lean_object* v_k_4145_, lean_object* v_t_4146_, lean_object* v_h_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4144_, v_k_4145_, v_t_4146_, v_h_4147_);
lean_dec(v_k_4145_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4149_, lean_object* v_binders_4150_, lean_object* v_docComment_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
uint8_t v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = l_Lean_isVersoDocComment(v_docComment_4151_);
v___x_4160_ = l_Lean_addDocStringOf(v___x_4159_, v_declName_4149_, v_binders_4150_, v_docComment_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4161_, lean_object* v_binders_4162_, lean_object* v_docComment_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_addDocString(v_declName_4161_, v_binders_4162_, v_docComment_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
return v_res_4171_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4172_, lean_object* v_binders_4173_, lean_object* v_docString_x3f_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4174_) == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
lean_dec(v_binders_4173_);
lean_dec(v_declName_4172_);
v___x_4182_ = lean_box(0);
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
else
{
lean_object* v_val_4184_; lean_object* v___x_4185_; 
v_val_4184_ = lean_ctor_get(v_docString_x3f_4174_, 0);
lean_inc(v_val_4184_);
lean_dec_ref_known(v_docString_x3f_4174_, 1);
v___x_4185_ = l_Lean_addDocString(v_declName_4172_, v_binders_4173_, v_val_4184_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_);
return v___x_4185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4186_, lean_object* v_binders_4187_, lean_object* v_docString_x3f_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_addDocString_x27(v_declName_4186_, v_binders_4187_, v_docString_x3f_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; lean_object* v_nextMacroScope_4202_; lean_object* v_ngen_4203_; lean_object* v_auxDeclNGen_4204_; lean_object* v_traceState_4205_; lean_object* v_messages_4206_; lean_object* v_infoState_4207_; lean_object* v_snapshotTasks_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4234_; 
v___x_4201_ = lean_st_ref_take(v___y_4199_);
v_nextMacroScope_4202_ = lean_ctor_get(v___x_4201_, 1);
v_ngen_4203_ = lean_ctor_get(v___x_4201_, 2);
v_auxDeclNGen_4204_ = lean_ctor_get(v___x_4201_, 3);
v_traceState_4205_ = lean_ctor_get(v___x_4201_, 4);
v_messages_4206_ = lean_ctor_get(v___x_4201_, 6);
v_infoState_4207_ = lean_ctor_get(v___x_4201_, 7);
v_snapshotTasks_4208_ = lean_ctor_get(v___x_4201_, 8);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4234_ == 0)
{
lean_object* v_unused_4235_; lean_object* v_unused_4236_; 
v_unused_4235_ = lean_ctor_get(v___x_4201_, 5);
lean_dec(v_unused_4235_);
v_unused_4236_ = lean_ctor_get(v___x_4201_, 0);
lean_dec(v_unused_4236_);
v___x_4210_ = v___x_4201_;
v_isShared_4211_ = v_isSharedCheck_4234_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_snapshotTasks_4208_);
lean_inc(v_infoState_4207_);
lean_inc(v_messages_4206_);
lean_inc(v_traceState_4205_);
lean_inc(v_auxDeclNGen_4204_);
lean_inc(v_ngen_4203_);
lean_inc(v_nextMacroScope_4202_);
lean_dec(v___x_4201_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4234_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4212_; lean_object* v___x_4214_; 
v___x_4212_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 5, v___x_4212_);
lean_ctor_set(v___x_4210_, 0, v_env_4197_);
v___x_4214_ = v___x_4210_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_env_4197_);
lean_ctor_set(v_reuseFailAlloc_4233_, 1, v_nextMacroScope_4202_);
lean_ctor_set(v_reuseFailAlloc_4233_, 2, v_ngen_4203_);
lean_ctor_set(v_reuseFailAlloc_4233_, 3, v_auxDeclNGen_4204_);
lean_ctor_set(v_reuseFailAlloc_4233_, 4, v_traceState_4205_);
lean_ctor_set(v_reuseFailAlloc_4233_, 5, v___x_4212_);
lean_ctor_set(v_reuseFailAlloc_4233_, 6, v_messages_4206_);
lean_ctor_set(v_reuseFailAlloc_4233_, 7, v_infoState_4207_);
lean_ctor_set(v_reuseFailAlloc_4233_, 8, v_snapshotTasks_4208_);
v___x_4214_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v_mctx_4217_; lean_object* v_zetaDeltaFVarIds_4218_; lean_object* v_postponed_4219_; lean_object* v_diag_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4231_; 
v___x_4215_ = lean_st_ref_set(v___y_4199_, v___x_4214_);
v___x_4216_ = lean_st_ref_take(v___y_4198_);
v_mctx_4217_ = lean_ctor_get(v___x_4216_, 0);
v_zetaDeltaFVarIds_4218_ = lean_ctor_get(v___x_4216_, 2);
v_postponed_4219_ = lean_ctor_get(v___x_4216_, 3);
v_diag_4220_ = lean_ctor_get(v___x_4216_, 4);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v___x_4216_, 1);
lean_dec(v_unused_4232_);
v___x_4222_ = v___x_4216_;
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_diag_4220_);
lean_inc(v_postponed_4219_);
lean_inc(v_zetaDeltaFVarIds_4218_);
lean_inc(v_mctx_4217_);
lean_dec(v___x_4216_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4231_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4224_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 1, v___x_4224_);
v___x_4226_ = v___x_4222_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_mctx_4217_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v_zetaDeltaFVarIds_4218_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v_postponed_4219_);
lean_ctor_set(v_reuseFailAlloc_4230_, 4, v_diag_4220_);
v___x_4226_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4227_ = lean_st_ref_set(v___y_4198_, v___x_4226_);
v___x_4228_ = lean_box(0);
v___x_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4228_);
return v___x_4229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec(v___y_4238_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4242_, lean_object* v_as_4243_, size_t v_i_4244_, size_t v_stop_4245_, lean_object* v_b_4246_){
_start:
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_usize_dec_eq(v_i_4244_, v_stop_4245_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; lean_object* v_index_4249_; lean_object* v_sourceString_4250_; lean_object* v_imports_4251_; lean_object* v_currNamespace_4252_; lean_object* v_openDecls_4253_; lean_object* v_options_4254_; lean_object* v_check_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4271_; 
v___x_4248_ = lean_array_uget(v_as_4243_, v_i_4244_);
v_index_4249_ = lean_ctor_get(v___x_4248_, 1);
v_sourceString_4250_ = lean_ctor_get(v___x_4248_, 2);
v_imports_4251_ = lean_ctor_get(v___x_4248_, 3);
v_currNamespace_4252_ = lean_ctor_get(v___x_4248_, 4);
v_openDecls_4253_ = lean_ctor_get(v___x_4248_, 5);
v_options_4254_ = lean_ctor_get(v___x_4248_, 6);
v_check_4255_ = lean_ctor_get(v___x_4248_, 7);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4271_ == 0)
{
lean_object* v_unused_4272_; 
v_unused_4272_ = lean_ctor_get(v___x_4248_, 0);
lean_dec(v_unused_4272_);
v___x_4257_ = v___x_4248_;
v_isShared_4258_ = v_isSharedCheck_4271_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_check_4255_);
lean_inc(v_options_4254_);
lean_inc(v_openDecls_4253_);
lean_inc(v_currNamespace_4252_);
lean_inc(v_imports_4251_);
lean_inc(v_sourceString_4250_);
lean_inc(v_index_4249_);
lean_dec(v___x_4248_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4271_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; lean_object* v_toEnvExtension_4260_; lean_object* v_asyncMode_4261_; lean_object* v___x_4262_; lean_object* v___x_4264_; 
v___x_4259_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4260_ = lean_ctor_get(v___x_4259_, 0);
v_asyncMode_4261_ = lean_ctor_get(v_toEnvExtension_4260_, 2);
lean_inc(v_n_4242_);
v___x_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4262_, 0, v_n_4242_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4262_);
v___x_4264_ = v___x_4257_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v___x_4262_);
lean_ctor_set(v_reuseFailAlloc_4270_, 1, v_index_4249_);
lean_ctor_set(v_reuseFailAlloc_4270_, 2, v_sourceString_4250_);
lean_ctor_set(v_reuseFailAlloc_4270_, 3, v_imports_4251_);
lean_ctor_set(v_reuseFailAlloc_4270_, 4, v_currNamespace_4252_);
lean_ctor_set(v_reuseFailAlloc_4270_, 5, v_openDecls_4253_);
lean_ctor_set(v_reuseFailAlloc_4270_, 6, v_options_4254_);
lean_ctor_set(v_reuseFailAlloc_4270_, 7, v_check_4255_);
v___x_4264_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; size_t v___x_4267_; size_t v___x_4268_; 
v___x_4265_ = lean_box(0);
v___x_4266_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4259_, v_b_4246_, v___x_4264_, v_asyncMode_4261_, v___x_4265_);
v___x_4267_ = ((size_t)1ULL);
v___x_4268_ = lean_usize_add(v_i_4244_, v___x_4267_);
v_i_4244_ = v___x_4268_;
v_b_4246_ = v___x_4266_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4242_);
return v_b_4246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4273_, lean_object* v_as_4274_, lean_object* v_i_4275_, lean_object* v_stop_4276_, lean_object* v_b_4277_){
_start:
{
size_t v_i_boxed_4278_; size_t v_stop_boxed_4279_; lean_object* v_res_4280_; 
v_i_boxed_4278_ = lean_unbox_usize(v_i_4275_);
lean_dec(v_i_4275_);
v_stop_boxed_4279_ = lean_unbox_usize(v_stop_4276_);
lean_dec(v_stop_4276_);
v_res_4280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4273_, v_as_4274_, v_i_boxed_4278_, v_stop_boxed_4279_, v_b_4277_);
lean_dec_ref(v_as_4274_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4281_, lean_object* v_deferred_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v_env_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4290_ = lean_st_ref_get(v___y_4288_);
v_env_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc_ref(v_env_4291_);
lean_dec(v___x_4290_);
v___x_4292_ = l_Lean_getMainModuleDoc(v_env_4291_);
v___x_4293_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4292_);
lean_dec_ref(v___x_4292_);
if (v___x_4293_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
lean_dec_ref(v_docs_4281_);
v___x_4294_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4294_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; lean_object* v_env_4297_; lean_object* v___x_4298_; lean_object* v_size_4299_; lean_object* v___x_4300_; lean_object* v_env_4301_; lean_object* v___x_4302_; 
v___x_4296_ = lean_st_ref_get(v___y_4288_);
v_env_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc_ref(v_env_4297_);
lean_dec(v___x_4296_);
v___x_4298_ = l_Lean_getMainVersoModuleDocs(v_env_4297_);
v_size_4299_ = lean_ctor_get(v___x_4298_, 2);
lean_inc(v_size_4299_);
lean_dec_ref(v___x_4298_);
v___x_4300_ = lean_st_ref_get(v___y_4288_);
v_env_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc_ref(v_env_4301_);
lean_dec(v___x_4300_);
v___x_4302_ = l_Lean_addVersoModuleDocSnippet(v_env_4301_, v_docs_4281_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
lean_dec(v_size_4299_);
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4305_ = l_Lean_stringToMessageData(v_a_4303_);
v___x_4306_ = l_Lean_indentD(v___x_4305_);
v___x_4307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4304_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4307_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
return v___x_4308_;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v_a_4309_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4310_ = lean_unsigned_to_nat(0u);
v___x_4311_ = lean_array_get_size(v_deferred_4282_);
v___x_4312_ = lean_nat_dec_lt(v___x_4310_, v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; 
lean_dec(v_size_4299_);
v___x_4313_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4309_, v___y_4286_, v___y_4288_);
return v___x_4313_;
}
else
{
uint8_t v___x_4314_; 
v___x_4314_ = lean_nat_dec_le(v___x_4311_, v___x_4311_);
if (v___x_4314_ == 0)
{
if (v___x_4312_ == 0)
{
lean_object* v___x_4315_; 
lean_dec(v_size_4299_);
v___x_4315_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4309_, v___y_4286_, v___y_4288_);
return v___x_4315_;
}
else
{
size_t v___x_4316_; size_t v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4316_ = ((size_t)0ULL);
v___x_4317_ = lean_usize_of_nat(v___x_4311_);
v___x_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4299_, v_deferred_4282_, v___x_4316_, v___x_4317_, v_a_4309_);
v___x_4319_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4318_, v___y_4286_, v___y_4288_);
return v___x_4319_;
}
}
else
{
size_t v___x_4320_; size_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4320_ = ((size_t)0ULL);
v___x_4321_ = lean_usize_of_nat(v___x_4311_);
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4299_, v_deferred_4282_, v___x_4320_, v___x_4321_, v_a_4309_);
v___x_4323_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4322_, v___y_4286_, v___y_4288_);
return v___x_4323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4324_, lean_object* v_deferred_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4324_, v_deferred_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec_ref(v_deferred_4325_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4334_, lean_object* v_docComment_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_Lean_versoModDocString(v_range_4334_, v_docComment_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; lean_object* v_fst_4345_; lean_object* v_snd_4346_; lean_object* v___x_4347_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4343_, 1);
v_fst_4345_ = lean_ctor_get(v_a_4344_, 0);
lean_inc(v_fst_4345_);
v_snd_4346_ = lean_ctor_get(v_a_4344_, 1);
lean_inc(v_snd_4346_);
lean_dec(v_a_4344_);
v___x_4347_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4345_, v_snd_4346_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
lean_dec(v_snd_4346_);
return v___x_4347_;
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4343_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4343_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4343_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4356_, lean_object* v_docComment_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_addVersoModDocString(v_range_4356_, v_docComment_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_docComment_4357_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4366_, v___y_4370_, v___y_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4383_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
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
res = runtime_initialize_Lean_DocString_DeferredCheck(builtin);
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
lean_object* initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
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
res = initialize_Lean_DocString_DeferredCheck(builtin);
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
