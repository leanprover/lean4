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
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_pmctx_280_, 4);
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
lean_dec_ref_known(v_pmctx_280_, 4);
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
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = l_Lean_Syntax_getTailPos_x3f(v___x_432_, v___x_433_);
lean_dec(v___x_432_);
if (lean_obj_tag(v___x_436_) == 1)
{
lean_object* v_val_437_; lean_object* v_source_438_; lean_object* v___y_440_; lean_object* v___x_444_; lean_object* v_endPos_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
lean_dec_ref(v_inst_429_);
lean_dec(v_docComment_419_);
v_val_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_val_437_);
lean_dec_ref_known(v___x_436_, 1);
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
lean_dec_ref_known(v_kind_484_, 2);
v_str_495_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_495_);
lean_dec_ref_known(v_pre_485_, 2);
v_str_496_ = lean_ctor_get(v_pre_486_, 1);
lean_inc_ref(v_str_496_);
lean_dec_ref_known(v_pre_486_, 2);
v_str_497_ = lean_ctor_get(v_pre_487_, 1);
lean_inc_ref(v_str_497_);
lean_dec_ref_known(v_pre_487_, 2);
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
lean_dec_ref_known(v_pre_487_, 2);
lean_dec(v_pre_488_);
lean_dec_ref_known(v_pre_486_, 2);
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_kind_484_, 2);
lean_dec_ref_known(v___x_483_, 3);
lean_dec_ref(v_toApplicative_470_);
v___x_524_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; 
lean_dec(v_pre_487_);
lean_dec_ref_known(v_pre_486_, 2);
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_kind_484_, 2);
lean_dec_ref_known(v___x_483_, 3);
lean_dec_ref(v_toApplicative_470_);
v___x_525_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; 
lean_dec(v_pre_486_);
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_kind_484_, 2);
lean_dec_ref_known(v___x_483_, 3);
lean_dec_ref(v_toApplicative_470_);
v___x_526_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; 
lean_dec(v_pre_485_);
lean_dec_ref_known(v_kind_484_, 2);
lean_dec_ref_known(v___x_483_, 3);
lean_dec_ref(v_toApplicative_470_);
v___x_527_ = lean_apply_4(v_toBind_471_, lean_box(0), lean_box(0), v_inst_463_, v___f_474_);
return v___x_527_;
}
}
else
{
lean_object* v___x_528_; 
lean_dec(v_kind_484_);
lean_dec_ref_known(v___x_483_, 3);
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
lean_dec_ref_known(v_pmctx_667_, 4);
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
lean_dec_ref_known(v_pmctx_667_, 4);
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
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = l_Lean_Syntax_getTailPos_x3f(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_val_793_; lean_object* v___f_794_; lean_object* v___x_795_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_val_793_);
lean_dec_ref_known(v___x_792_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_828_, lean_object* v_declName_829_, lean_object* v_binders_830_, lean_object* v___x_831_, uint8_t v___x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_828_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Doc_DocM_exec___redArg(v_declName_829_, v_binders_830_, v___x_831_, v___x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v_fileName_842_; lean_object* v_options_843_; lean_object* v_currRecDepth_844_; lean_object* v_maxRecDepth_845_; lean_object* v_ref_846_; lean_object* v_currNamespace_847_; lean_object* v_openDecls_848_; lean_object* v_initHeartbeats_849_; lean_object* v_maxHeartbeats_850_; lean_object* v_quotContext_851_; lean_object* v_currMacroScope_852_; uint8_t v_diag_853_; lean_object* v_cancelTk_x3f_854_; uint8_t v_suppressElabErrors_855_; lean_object* v_inheritedTraceOptions_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_val_841_ = lean_ctor_get(v_fileMap_x3f_828_, 0);
v_fileName_842_ = lean_ctor_get(v___y_837_, 0);
v_options_843_ = lean_ctor_get(v___y_837_, 2);
v_currRecDepth_844_ = lean_ctor_get(v___y_837_, 3);
v_maxRecDepth_845_ = lean_ctor_get(v___y_837_, 4);
v_ref_846_ = lean_ctor_get(v___y_837_, 5);
v_currNamespace_847_ = lean_ctor_get(v___y_837_, 6);
v_openDecls_848_ = lean_ctor_get(v___y_837_, 7);
v_initHeartbeats_849_ = lean_ctor_get(v___y_837_, 8);
v_maxHeartbeats_850_ = lean_ctor_get(v___y_837_, 9);
v_quotContext_851_ = lean_ctor_get(v___y_837_, 10);
v_currMacroScope_852_ = lean_ctor_get(v___y_837_, 11);
v_diag_853_ = lean_ctor_get_uint8(v___y_837_, sizeof(void*)*14);
v_cancelTk_x3f_854_ = lean_ctor_get(v___y_837_, 12);
v_suppressElabErrors_855_ = lean_ctor_get_uint8(v___y_837_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_856_ = lean_ctor_get(v___y_837_, 13);
lean_inc_ref(v_inheritedTraceOptions_856_);
lean_inc(v_cancelTk_x3f_854_);
lean_inc(v_currMacroScope_852_);
lean_inc(v_quotContext_851_);
lean_inc(v_maxHeartbeats_850_);
lean_inc(v_initHeartbeats_849_);
lean_inc(v_openDecls_848_);
lean_inc(v_currNamespace_847_);
lean_inc(v_ref_846_);
lean_inc(v_maxRecDepth_845_);
lean_inc(v_currRecDepth_844_);
lean_inc_ref(v_options_843_);
lean_inc(v_val_841_);
lean_inc_ref(v_fileName_842_);
v___x_857_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_857_, 0, v_fileName_842_);
lean_ctor_set(v___x_857_, 1, v_val_841_);
lean_ctor_set(v___x_857_, 2, v_options_843_);
lean_ctor_set(v___x_857_, 3, v_currRecDepth_844_);
lean_ctor_set(v___x_857_, 4, v_maxRecDepth_845_);
lean_ctor_set(v___x_857_, 5, v_ref_846_);
lean_ctor_set(v___x_857_, 6, v_currNamespace_847_);
lean_ctor_set(v___x_857_, 7, v_openDecls_848_);
lean_ctor_set(v___x_857_, 8, v_initHeartbeats_849_);
lean_ctor_set(v___x_857_, 9, v_maxHeartbeats_850_);
lean_ctor_set(v___x_857_, 10, v_quotContext_851_);
lean_ctor_set(v___x_857_, 11, v_currMacroScope_852_);
lean_ctor_set(v___x_857_, 12, v_cancelTk_x3f_854_);
lean_ctor_set(v___x_857_, 13, v_inheritedTraceOptions_856_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*14, v_diag_853_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*14 + 1, v_suppressElabErrors_855_);
v___x_858_ = l_Lean_Doc_DocM_exec___redArg(v_declName_829_, v_binders_830_, v___x_831_, v___x_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___x_857_, v___y_838_);
lean_dec_ref_known(v___x_857_, 14);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_859_, lean_object* v_declName_860_, lean_object* v_binders_861_, lean_object* v___x_862_, lean_object* v___x_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_9417__boxed_871_; lean_object* v_res_872_; 
v___x_9417__boxed_871_ = lean_unbox(v___x_863_);
v_res_872_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_859_, v_declName_860_, v_binders_861_, v___x_862_, v___x_9417__boxed_871_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v_fileMap_x3f_859_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_873_, size_t v_i_874_, lean_object* v_bs_875_){
_start:
{
uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_lt(v_i_874_, v_sz_873_);
if (v___x_876_ == 0)
{
return v_bs_875_;
}
else
{
lean_object* v_v_877_; lean_object* v___x_878_; lean_object* v_bs_x27_879_; size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_v_877_ = lean_array_uget(v_bs_875_, v_i_874_);
v___x_878_ = lean_unsigned_to_nat(0u);
v_bs_x27_879_ = lean_array_uset(v_bs_875_, v_i_874_, v___x_878_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_874_, v___x_880_);
v___x_882_ = lean_array_uset(v_bs_x27_879_, v_i_874_, v_v_877_);
v_i_874_ = v___x_881_;
v_bs_875_ = v___x_882_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_884_, lean_object* v_i_885_, lean_object* v_bs_886_){
_start:
{
size_t v_sz_boxed_887_; size_t v_i_boxed_888_; lean_object* v_res_889_; 
v_sz_boxed_887_ = lean_unbox_usize(v_sz_884_);
lean_dec(v_sz_884_);
v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_res_889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_887_, v_i_boxed_888_, v_bs_886_);
return v_res_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_890_, lean_object* v_opt_891_){
_start:
{
lean_object* v_name_892_; lean_object* v_defValue_893_; lean_object* v_map_894_; lean_object* v___x_895_; 
v_name_892_ = lean_ctor_get(v_opt_891_, 0);
v_defValue_893_ = lean_ctor_get(v_opt_891_, 1);
v_map_894_ = lean_ctor_get(v_opts_890_, 0);
v___x_895_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_894_, v_name_892_);
if (lean_obj_tag(v___x_895_) == 0)
{
uint8_t v___x_896_; 
v___x_896_ = lean_unbox(v_defValue_893_);
return v___x_896_;
}
else
{
lean_object* v_val_897_; 
v_val_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_895_, 1);
if (lean_obj_tag(v_val_897_) == 1)
{
uint8_t v_v_898_; 
v_v_898_ = lean_ctor_get_uint8(v_val_897_, 0);
lean_dec_ref_known(v_val_897_, 0);
return v_v_898_;
}
else
{
uint8_t v___x_899_; 
lean_dec(v_val_897_);
v___x_899_ = lean_unbox(v_defValue_893_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_900_, lean_object* v_opt_901_){
_start:
{
uint8_t v_res_902_; lean_object* v_r_903_; 
v_res_902_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_900_, v_opt_901_);
lean_dec_ref(v_opt_901_);
lean_dec_ref(v_opts_900_);
v_r_903_ = lean_box(v_res_902_);
return v_r_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_env_911_; lean_object* v___x_912_; lean_object* v_mctx_913_; lean_object* v_lctx_914_; lean_object* v_options_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_910_ = lean_st_ref_get(v___y_908_);
v_env_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_env_911_);
lean_dec(v___x_910_);
v___x_912_ = lean_st_ref_get(v___y_906_);
v_mctx_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc_ref(v_mctx_913_);
lean_dec(v___x_912_);
v_lctx_914_ = lean_ctor_get(v___y_905_, 2);
v_options_915_ = lean_ctor_get(v___y_907_, 2);
lean_inc_ref(v_options_915_);
lean_inc_ref(v_lctx_914_);
v___x_916_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_916_, 0, v_env_911_);
lean_ctor_set(v___x_916_, 1, v_mctx_913_);
lean_ctor_set(v___x_916_, 2, v_lctx_914_);
lean_ctor_set(v___x_916_, 3, v_options_915_);
v___x_917_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_msgData_904_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v___y_934_, uint8_t v_suppressElabErrors_935_, lean_object* v_x_936_){
_start:
{
if (lean_obj_tag(v_x_936_) == 1)
{
lean_object* v_pre_937_; 
v_pre_937_ = lean_ctor_get(v_x_936_, 0);
switch(lean_obj_tag(v_pre_937_))
{
case 1:
{
lean_object* v_pre_938_; 
v_pre_938_ = lean_ctor_get(v_pre_937_, 0);
switch(lean_obj_tag(v_pre_938_))
{
case 0:
{
lean_object* v_str_939_; lean_object* v_str_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_str_939_ = lean_ctor_get(v_x_936_, 1);
v_str_940_ = lean_ctor_get(v_pre_937_, 1);
v___x_941_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_942_ = lean_string_dec_eq(v_str_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_944_ = lean_string_dec_eq(v_str_940_, v___x_943_);
if (v___x_944_ == 0)
{
return v___y_934_;
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_946_ = lean_string_dec_eq(v_str_939_, v___x_945_);
if (v___x_946_ == 0)
{
return v___y_934_;
}
else
{
return v_suppressElabErrors_935_;
}
}
}
else
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_948_ = lean_string_dec_eq(v_str_939_, v___x_947_);
if (v___x_948_ == 0)
{
return v___y_934_;
}
else
{
return v_suppressElabErrors_935_;
}
}
}
case 1:
{
lean_object* v_pre_949_; 
v_pre_949_ = lean_ctor_get(v_pre_938_, 0);
if (lean_obj_tag(v_pre_949_) == 0)
{
lean_object* v_str_950_; lean_object* v_str_951_; lean_object* v_str_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_str_950_ = lean_ctor_get(v_x_936_, 1);
v_str_951_ = lean_ctor_get(v_pre_937_, 1);
v_str_952_ = lean_ctor_get(v_pre_938_, 1);
v___x_953_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_954_ = lean_string_dec_eq(v_str_952_, v___x_953_);
if (v___x_954_ == 0)
{
return v___y_934_;
}
else
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_956_ = lean_string_dec_eq(v_str_951_, v___x_955_);
if (v___x_956_ == 0)
{
return v___y_934_;
}
else
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_958_ = lean_string_dec_eq(v_str_950_, v___x_957_);
if (v___x_958_ == 0)
{
return v___y_934_;
}
else
{
return v_suppressElabErrors_935_;
}
}
}
}
else
{
return v___y_934_;
}
}
default: 
{
return v___y_934_;
}
}
}
case 0:
{
lean_object* v_str_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_str_959_ = lean_ctor_get(v_x_936_, 1);
v___x_960_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_961_ = lean_string_dec_eq(v_str_959_, v___x_960_);
if (v___x_961_ == 0)
{
return v___y_934_;
}
else
{
return v_suppressElabErrors_935_;
}
}
default: 
{
return v___y_934_;
}
}
}
else
{
return v___y_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v___y_962_, lean_object* v_suppressElabErrors_963_, lean_object* v_x_964_){
_start:
{
uint8_t v___y_9514__boxed_965_; uint8_t v_suppressElabErrors_boxed_966_; uint8_t v_res_967_; lean_object* v_r_968_; 
v___y_9514__boxed_965_ = lean_unbox(v___y_962_);
v_suppressElabErrors_boxed_966_ = lean_unbox(v_suppressElabErrors_963_);
v_res_967_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v___y_9514__boxed_965_, v_suppressElabErrors_boxed_966_, v_x_964_);
lean_dec(v_x_964_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_969_, lean_object* v_msgData_970_, uint8_t v_severity_971_, uint8_t v_isSilent_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; uint8_t v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; uint8_t v___y_1019_; uint8_t v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; uint8_t v___y_1045_; uint8_t v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; uint8_t v___y_1056_; uint8_t v___y_1057_; uint8_t v___x_1062_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; uint8_t v___y_1068_; uint8_t v___y_1069_; uint8_t v___y_1070_; uint8_t v___y_1072_; uint8_t v___x_1087_; 
v___x_1062_ = 2;
v___x_1087_ = l_Lean_instBEqMessageSeverity_beq(v_severity_971_, v___x_1062_);
if (v___x_1087_ == 0)
{
v___y_1072_ = v___x_1087_;
goto v___jp_1071_;
}
else
{
uint8_t v___x_1088_; 
lean_inc_ref(v_msgData_970_);
v___x_1088_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_970_);
v___y_1072_ = v___x_1088_;
goto v___jp_1071_;
}
v___jp_978_:
{
lean_object* v___x_988_; lean_object* v_currNamespace_989_; lean_object* v_openDecls_990_; lean_object* v_env_991_; lean_object* v_nextMacroScope_992_; lean_object* v_ngen_993_; lean_object* v_auxDeclNGen_994_; lean_object* v_traceState_995_; lean_object* v_cache_996_; lean_object* v_messages_997_; lean_object* v_infoState_998_; lean_object* v_snapshotTasks_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1013_; 
v___x_988_ = lean_st_ref_take(v___y_987_);
v_currNamespace_989_ = lean_ctor_get(v___y_986_, 6);
v_openDecls_990_ = lean_ctor_get(v___y_986_, 7);
v_env_991_ = lean_ctor_get(v___x_988_, 0);
v_nextMacroScope_992_ = lean_ctor_get(v___x_988_, 1);
v_ngen_993_ = lean_ctor_get(v___x_988_, 2);
v_auxDeclNGen_994_ = lean_ctor_get(v___x_988_, 3);
v_traceState_995_ = lean_ctor_get(v___x_988_, 4);
v_cache_996_ = lean_ctor_get(v___x_988_, 5);
v_messages_997_ = lean_ctor_get(v___x_988_, 6);
v_infoState_998_ = lean_ctor_get(v___x_988_, 7);
v_snapshotTasks_999_ = lean_ctor_get(v___x_988_, 8);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1001_ = v___x_988_;
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snapshotTasks_999_);
lean_inc(v_infoState_998_);
lean_inc(v_messages_997_);
lean_inc(v_cache_996_);
lean_inc(v_traceState_995_);
lean_inc(v_auxDeclNGen_994_);
lean_inc(v_ngen_993_);
lean_inc(v_nextMacroScope_992_);
lean_inc(v_env_991_);
lean_dec(v___x_988_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1013_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
lean_inc(v_openDecls_990_);
lean_inc(v_currNamespace_989_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_currNamespace_989_);
lean_ctor_set(v___x_1003_, 1, v_openDecls_990_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___y_983_);
lean_inc_ref(v___y_984_);
lean_inc_ref(v___y_980_);
v___x_1005_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1005_, 0, v___y_980_);
lean_ctor_set(v___x_1005_, 1, v___y_979_);
lean_ctor_set(v___x_1005_, 2, v___y_982_);
lean_ctor_set(v___x_1005_, 3, v___y_984_);
lean_ctor_set(v___x_1005_, 4, v___x_1004_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*5, v___y_981_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*5 + 1, v___y_985_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*5 + 2, v_isSilent_972_);
v___x_1006_ = l_Lean_MessageLog_add(v___x_1005_, v_messages_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 6, v___x_1006_);
v___x_1008_ = v___x_1001_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_env_991_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_nextMacroScope_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_ngen_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_auxDeclNGen_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_traceState_995_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_cache_996_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v_infoState_998_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_snapshotTasks_999_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_st_ref_set(v___y_987_, v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1038_; 
v___x_1023_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_970_);
v___x_1024_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_1023_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1038_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_inc_ref_n(v___y_1018_, 2);
v___x_1029_ = l_Lean_FileMap_toPosition(v___y_1018_, v___y_1017_);
lean_dec(v___y_1017_);
v___x_1030_ = l_Lean_FileMap_toPosition(v___y_1018_, v___y_1022_);
lean_dec(v___y_1022_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1020_ == 0)
{
lean_del_object(v___x_1027_);
lean_dec_ref(v___y_1015_);
v___y_979_ = v___x_1029_;
v___y_980_ = v___y_1016_;
v___y_981_ = v___y_1019_;
v___y_982_ = v___x_1031_;
v___y_983_ = v_a_1025_;
v___y_984_ = v___x_1032_;
v___y_985_ = v___y_1021_;
v___y_986_ = v___y_975_;
v___y_987_ = v___y_976_;
goto v___jp_978_;
}
else
{
uint8_t v___x_1033_; 
lean_inc(v_a_1025_);
v___x_1033_ = l_Lean_MessageData_hasTag(v___y_1015_, v_a_1025_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec_ref_known(v___x_1031_, 1);
lean_dec_ref(v___x_1029_);
lean_dec(v_a_1025_);
v___x_1034_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1034_);
v___x_1036_ = v___x_1027_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_del_object(v___x_1027_);
v___y_979_ = v___x_1029_;
v___y_980_ = v___y_1016_;
v___y_981_ = v___y_1019_;
v___y_982_ = v___x_1031_;
v___y_983_ = v_a_1025_;
v___y_984_ = v___x_1032_;
v___y_985_ = v___y_1021_;
v___y_986_ = v___y_975_;
v___y_987_ = v___y_976_;
goto v___jp_978_;
}
}
}
}
v___jp_1039_:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Syntax_getTailPos_x3f(v___y_1042_, v___y_1044_);
lean_dec(v___y_1042_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_inc(v___y_1047_);
v___y_1015_ = v___y_1040_;
v___y_1016_ = v___y_1041_;
v___y_1017_ = v___y_1047_;
v___y_1018_ = v___y_1043_;
v___y_1019_ = v___y_1044_;
v___y_1020_ = v___y_1045_;
v___y_1021_ = v___y_1046_;
v___y_1022_ = v___y_1047_;
goto v___jp_1014_;
}
else
{
lean_object* v_val_1049_; 
v_val_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___y_1015_ = v___y_1040_;
v___y_1016_ = v___y_1041_;
v___y_1017_ = v___y_1047_;
v___y_1018_ = v___y_1043_;
v___y_1019_ = v___y_1044_;
v___y_1020_ = v___y_1045_;
v___y_1021_ = v___y_1046_;
v___y_1022_ = v_val_1049_;
goto v___jp_1014_;
}
}
v___jp_1050_:
{
lean_object* v_ref_1058_; lean_object* v___x_1059_; 
v_ref_1058_ = l_Lean_replaceRef(v_ref_969_, v___y_1052_);
v___x_1059_ = l_Lean_Syntax_getPos_x3f(v_ref_1058_, v___y_1055_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v_ref_1058_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1055_;
v___y_1045_ = v___y_1056_;
v___y_1046_ = v___y_1057_;
v___y_1047_ = v___x_1060_;
goto v___jp_1039_;
}
else
{
lean_object* v_val_1061_; 
v_val_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v___x_1059_, 1);
v___y_1040_ = v___y_1051_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v_ref_1058_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1055_;
v___y_1045_ = v___y_1056_;
v___y_1046_ = v___y_1057_;
v___y_1047_ = v_val_1061_;
goto v___jp_1039_;
}
}
v___jp_1063_:
{
if (v___y_1070_ == 0)
{
v___y_1051_ = v___y_1066_;
v___y_1052_ = v___y_1064_;
v___y_1053_ = v___y_1065_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1069_;
v___y_1056_ = v___y_1068_;
v___y_1057_ = v_severity_971_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v___y_1066_;
v___y_1052_ = v___y_1064_;
v___y_1053_ = v___y_1065_;
v___y_1054_ = v___y_1067_;
v___y_1055_ = v___y_1069_;
v___y_1056_ = v___y_1068_;
v___y_1057_ = v___x_1062_;
goto v___jp_1050_;
}
}
v___jp_1071_:
{
if (v___y_1072_ == 0)
{
lean_object* v_fileName_1073_; lean_object* v_fileMap_1074_; lean_object* v_options_1075_; lean_object* v_ref_1076_; uint8_t v_suppressElabErrors_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; uint8_t v___x_1081_; uint8_t v___x_1082_; 
v_fileName_1073_ = lean_ctor_get(v___y_975_, 0);
v_fileMap_1074_ = lean_ctor_get(v___y_975_, 1);
v_options_1075_ = lean_ctor_get(v___y_975_, 2);
v_ref_1076_ = lean_ctor_get(v___y_975_, 5);
v_suppressElabErrors_1077_ = lean_ctor_get_uint8(v___y_975_, sizeof(void*)*14 + 1);
v___x_1078_ = lean_box(v___y_1072_);
v___x_1079_ = lean_box(v_suppressElabErrors_1077_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1080_, 0, v___x_1078_);
lean_closure_set(v___f_1080_, 1, v___x_1079_);
v___x_1081_ = 1;
v___x_1082_ = l_Lean_instBEqMessageSeverity_beq(v_severity_971_, v___x_1081_);
if (v___x_1082_ == 0)
{
v___y_1064_ = v_ref_1076_;
v___y_1065_ = v_fileName_1073_;
v___y_1066_ = v___f_1080_;
v___y_1067_ = v_fileMap_1074_;
v___y_1068_ = v_suppressElabErrors_1077_;
v___y_1069_ = v___y_1072_;
v___y_1070_ = v___x_1082_;
goto v___jp_1063_;
}
else
{
lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1083_ = l_Lean_warningAsError;
v___x_1084_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1075_, v___x_1083_);
v___y_1064_ = v_ref_1076_;
v___y_1065_ = v_fileName_1073_;
v___y_1066_ = v___f_1080_;
v___y_1067_ = v_fileMap_1074_;
v___y_1068_ = v_suppressElabErrors_1077_;
v___y_1069_ = v___y_1072_;
v___y_1070_ = v___x_1084_;
goto v___jp_1063_;
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec_ref(v_msgData_970_);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1089_, lean_object* v_msgData_1090_, lean_object* v_severity_1091_, lean_object* v_isSilent_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
uint8_t v_severity_boxed_1098_; uint8_t v_isSilent_boxed_1099_; lean_object* v_res_1100_; 
v_severity_boxed_1098_ = lean_unbox(v_severity_1091_);
v_isSilent_boxed_1099_ = lean_unbox(v_isSilent_1092_);
v_res_1100_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1089_, v_msgData_1090_, v_severity_boxed_1098_, v_isSilent_boxed_1099_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v_ref_1089_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1101_, size_t v_sz_1102_, size_t v_i_1103_, lean_object* v_b_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1103_, v_sz_1102_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_b_1104_);
return v___x_1113_;
}
else
{
lean_object* v_ref_1114_; lean_object* v_a_1115_; uint8_t v_severity_1116_; uint8_t v_isSilent_1117_; lean_object* v_data_1118_; lean_object* v___x_1119_; 
v_ref_1114_ = lean_ctor_get(v___y_1109_, 5);
v_a_1115_ = lean_array_uget_borrowed(v_as_1101_, v_i_1103_);
v_severity_1116_ = lean_ctor_get_uint8(v_a_1115_, sizeof(void*)*5 + 1);
v_isSilent_1117_ = lean_ctor_get_uint8(v_a_1115_, sizeof(void*)*5 + 2);
v_data_1118_ = lean_ctor_get(v_a_1115_, 4);
lean_inc(v_data_1118_);
v___x_1119_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1114_, v_data_1118_, v_severity_1116_, v_isSilent_1117_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; 
lean_dec_ref_known(v___x_1119_, 1);
v___x_1120_ = lean_box(0);
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1103_, v___x_1121_);
v_i_1103_ = v___x_1122_;
v_b_1104_ = v___x_1120_;
goto _start;
}
else
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1124_, lean_object* v_sz_1125_, lean_object* v_i_1126_, lean_object* v_b_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
size_t v_sz_boxed_1135_; size_t v_i_boxed_1136_; lean_object* v_res_1137_; 
v_sz_boxed_1135_ = lean_unbox_usize(v_sz_1125_);
lean_dec(v_sz_1125_);
v_i_boxed_1136_ = lean_unbox_usize(v_i_1126_);
lean_dec(v_i_1126_);
v_res_1137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1124_, v_sz_boxed_1135_, v_i_boxed_1136_, v_b_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_as_1124_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v_infoState_1142_; lean_object* v_env_1143_; lean_object* v_nextMacroScope_1144_; lean_object* v_ngen_1145_; lean_object* v_auxDeclNGen_1146_; lean_object* v_traceState_1147_; lean_object* v_cache_1148_; lean_object* v_messages_1149_; lean_object* v_snapshotTasks_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1170_; 
v___x_1141_ = lean_st_ref_take(v___y_1139_);
v_infoState_1142_ = lean_ctor_get(v___x_1141_, 7);
v_env_1143_ = lean_ctor_get(v___x_1141_, 0);
v_nextMacroScope_1144_ = lean_ctor_get(v___x_1141_, 1);
v_ngen_1145_ = lean_ctor_get(v___x_1141_, 2);
v_auxDeclNGen_1146_ = lean_ctor_get(v___x_1141_, 3);
v_traceState_1147_ = lean_ctor_get(v___x_1141_, 4);
v_cache_1148_ = lean_ctor_get(v___x_1141_, 5);
v_messages_1149_ = lean_ctor_get(v___x_1141_, 6);
v_snapshotTasks_1150_ = lean_ctor_get(v___x_1141_, 8);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1152_ = v___x_1141_;
v_isShared_1153_ = v_isSharedCheck_1170_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snapshotTasks_1150_);
lean_inc(v_infoState_1142_);
lean_inc(v_messages_1149_);
lean_inc(v_cache_1148_);
lean_inc(v_traceState_1147_);
lean_inc(v_auxDeclNGen_1146_);
lean_inc(v_ngen_1145_);
lean_inc(v_nextMacroScope_1144_);
lean_inc(v_env_1143_);
lean_dec(v___x_1141_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1170_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_assignment_1154_; lean_object* v_lazyAssignment_1155_; lean_object* v_trees_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1169_; 
v_assignment_1154_ = lean_ctor_get(v_infoState_1142_, 0);
v_lazyAssignment_1155_ = lean_ctor_get(v_infoState_1142_, 1);
v_trees_1156_ = lean_ctor_get(v_infoState_1142_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_infoState_1142_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1158_ = v_infoState_1142_;
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_trees_1156_);
lean_inc(v_lazyAssignment_1155_);
lean_inc(v_assignment_1154_);
lean_dec(v_infoState_1142_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1169_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_assignment_1154_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_lazyAssignment_1155_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_trees_1156_);
v___x_1161_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*3, v_flag_1138_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 7, v___x_1161_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_env_1143_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_nextMacroScope_1144_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_ngen_1145_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_auxDeclNGen_1146_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_traceState_1147_);
lean_ctor_set(v_reuseFailAlloc_1167_, 5, v_cache_1148_);
lean_ctor_set(v_reuseFailAlloc_1167_, 6, v_messages_1149_);
lean_ctor_set(v_reuseFailAlloc_1167_, 7, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 8, v_snapshotTasks_1150_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_st_ref_set(v___y_1139_, v___x_1163_);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_flag_boxed_1174_; lean_object* v_res_1175_; 
v_flag_boxed_1174_ = lean_unbox(v_flag_1171_);
v_res_1175_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1174_, v___y_1172_);
lean_dec(v___y_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v_infoState_1186_; uint8_t v_enabled_1187_; lean_object* v_a_1189_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1185_ = lean_st_ref_get(v___y_1183_);
v_infoState_1186_ = lean_ctor_get(v___x_1185_, 7);
lean_inc_ref(v_infoState_1186_);
lean_dec(v___x_1185_);
v_enabled_1187_ = lean_ctor_get_uint8(v_infoState_1186_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1186_);
v___x_1199_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1176_, v___y_1183_);
lean_dec_ref(v___x_1199_);
lean_inc(v___y_1183_);
lean_inc_ref(v___y_1182_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
v___x_1200_ = lean_apply_7(v_x_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, lean_box(0));
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v___x_1202_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1187_, v___y_1183_);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1202_, 0);
lean_dec(v_unused_1210_);
v___x_1204_ = v___x_1202_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v___x_1202_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v_a_1201_);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1201_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1211_; 
v_a_1211_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1200_, 1);
v_a_1189_ = v_a_1211_;
goto v___jp_1188_;
}
v___jp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
v___x_1190_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1187_, v___y_1183_);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1198_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set_tag(v___x_1192_, 1);
lean_ctor_set(v___x_1192_, 0, v_a_1189_);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1189_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_flag_boxed_1221_; lean_object* v_res_1222_; 
v_flag_boxed_1221_ = lean_unbox(v_flag_1212_);
v_res_1222_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1221_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1223_, lean_object* v_binders_1224_, lean_object* v_blocks_1225_, lean_object* v_fileMap_x3f_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1232_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v_a_1237_; size_t v_sz_1255_; size_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___y_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v_sz_1255_ = lean_array_size(v_blocks_1225_);
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1255_, v___x_1256_, v_blocks_1225_);
v___x_1258_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1258_, 0, v___x_1257_);
v___x_1259_ = 1;
v___x_1260_ = lean_box(v___x_1259_);
v___y_1261_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1261_, 0, v_fileMap_x3f_1226_);
lean_closure_set(v___y_1261_, 1, v_declName_1223_);
lean_closure_set(v___y_1261_, 2, v_binders_1224_);
lean_closure_set(v___y_1261_, 3, v___x_1258_);
lean_closure_set(v___y_1261_, 4, v___x_1260_);
v___x_1262_ = 0;
v___x_1263_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1262_, v___y_1261_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1232_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = l_Lean_Core_setMessageLog___redArg(v_a_1235_, v_a_1232_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; size_t v_sz_1270_; lean_object* v___x_1271_; 
lean_dec_ref_known(v___x_1267_, 1);
v___x_1268_ = l_Lean_MessageLog_toArray(v_a_1266_);
lean_dec(v_a_1266_);
v___x_1269_ = lean_box(0);
v_sz_1270_ = lean_array_size(v___x_1268_);
v___x_1271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1268_, v_sz_1270_, v___x_1256_, v___x_1269_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec_ref(v___x_1268_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1296_; 
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; 
v_unused_1297_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1297_);
v___x_1273_ = v___x_1271_;
v_isShared_1274_ = v_isSharedCheck_1296_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1296_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1295_; 
v_fst_1275_ = lean_ctor_get(v_a_1264_, 0);
v_snd_1276_ = lean_ctor_get(v_a_1264_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_a_1264_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1278_ = v_a_1264_;
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_inc(v_fst_1275_);
lean_dec(v_a_1264_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_fst_1280_; lean_object* v_snd_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1294_; 
v_fst_1280_ = lean_ctor_get(v_fst_1275_, 0);
v_snd_1281_ = lean_ctor_get(v_fst_1275_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_fst_1275_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1283_ = v_fst_1275_;
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_snd_1281_);
lean_inc(v_fst_1280_);
lean_dec(v_fst_1275_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_snd_1281_);
v___x_1286_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1286_);
v___x_1288_ = v___x_1278_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1276_);
v___x_1288_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1290_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1288_);
v___x_1290_ = v___x_1273_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_a_1264_);
v_a_1298_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1271_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1271_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1266_);
lean_dec(v_a_1264_);
v_a_1306_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1267_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1267_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; 
lean_dec(v_a_1264_);
v_a_1314_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1265_, 1);
v_a_1237_ = v_a_1314_;
goto v___jp_1236_;
}
}
else
{
lean_object* v_a_1315_; 
v_a_1315_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1315_);
lean_dec_ref_known(v___x_1263_, 1);
v_a_1237_ = v_a_1315_;
goto v___jp_1236_;
}
v___jp_1236_:
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Core_setMessageLog___redArg(v_a_1235_, v_a_1232_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1238_, 0);
lean_dec(v_unused_1246_);
v___x_1240_ = v___x_1238_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v___x_1238_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
lean_ctor_set(v___x_1240_, 0, v_a_1237_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1237_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_a_1237_);
v_a_1247_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1238_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1238_);
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
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_fileMap_x3f_1226_);
lean_dec_ref(v_blocks_1225_);
lean_dec(v_binders_1224_);
lean_dec(v_declName_1223_);
v_a_1316_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1234_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1234_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1324_, lean_object* v_binders_1325_, lean_object* v_blocks_1326_, lean_object* v_fileMap_x3f_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1324_, v_binders_1325_, v_blocks_1326_, v_fileMap_x3f_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1336_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
uint8_t v_flag_boxed_1353_; lean_object* v_res_1354_; 
v_flag_boxed_1353_ = lean_unbox(v_flag_1345_);
v_res_1354_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1353_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1355_, uint8_t v_flag_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_flag_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v_flag_boxed_1376_; lean_object* v_res_1377_; 
v_flag_boxed_1376_ = lean_unbox(v_flag_1367_);
v_res_1377_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1366_, v_flag_boxed_1376_, v_x_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1378_, lean_object* v_msgData_1379_, uint8_t v_severity_1380_, uint8_t v_isSilent_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1378_, v_msgData_1379_, v_severity_1380_, v_isSilent_1381_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1390_, lean_object* v_msgData_1391_, lean_object* v_severity_1392_, lean_object* v_isSilent_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
uint8_t v_severity_boxed_1401_; uint8_t v_isSilent_boxed_1402_; lean_object* v_res_1403_; 
v_severity_boxed_1401_ = lean_unbox(v_severity_1392_);
v_isSilent_boxed_1402_ = lean_unbox(v_isSilent_1393_);
v_res_1403_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1390_, v_msgData_1391_, v_severity_boxed_1401_, v_isSilent_boxed_1402_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v_ref_1390_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1404_, uint8_t v_severity_1405_, uint8_t v_isSilent_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; 
v_ref_1412_ = lean_ctor_get(v___y_1409_, 5);
v___x_1413_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1412_, v_msgData_1404_, v_severity_1405_, v_isSilent_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1414_, lean_object* v_severity_1415_, lean_object* v_isSilent_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v_severity_boxed_1422_; uint8_t v_isSilent_boxed_1423_; lean_object* v_res_1424_; 
v_severity_boxed_1422_ = lean_unbox(v_severity_1415_);
v_isSilent_boxed_1423_ = lean_unbox(v_isSilent_1416_);
v_res_1424_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1414_, v_severity_boxed_1422_, v_isSilent_boxed_1423_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
uint8_t v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = 2;
v___x_1434_ = 0;
v___x_1435_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1425_, v___x_1433_, v___x_1434_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1445_, size_t v_sz_1446_, size_t v_i_1447_, lean_object* v_b_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_usize_dec_lt(v_i_1447_, v_sz_1446_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1448_);
return v___x_1457_;
}
else
{
lean_object* v_a_1458_; lean_object* v_snd_1459_; lean_object* v_snd_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v_a_1458_ = lean_array_uget_borrowed(v_as_1445_, v_i_1447_);
v_snd_1459_ = lean_ctor_get(v_a_1458_, 1);
v_snd_1460_ = lean_ctor_get(v_snd_1459_, 1);
lean_inc(v_snd_1460_);
v___x_1461_ = l_Lean_Parser_Error_toString(v_snd_1460_);
v___x_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
v___x_1464_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1463_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; 
lean_dec_ref_known(v___x_1464_, 1);
v___x_1465_ = lean_box(0);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1447_, v___x_1466_);
v_i_1447_ = v___x_1467_;
v_b_1448_ = v___x_1465_;
goto _start;
}
else
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
size_t v_sz_boxed_1480_; size_t v_i_boxed_1481_; lean_object* v_res_1482_; 
v_sz_boxed_1480_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1481_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1469_, v_sz_boxed_1480_, v_i_boxed_1481_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1500_, lean_object* v_binders_1501_, lean_object* v_docComment_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; lean_object* v_env_1511_; lean_object* v_fileName_1512_; lean_object* v_options_1513_; lean_object* v_currNamespace_1514_; lean_object* v_openDecls_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1510_ = lean_st_ref_get(v_a_1508_);
v_env_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_ref_n(v_env_1511_, 2);
lean_dec(v___x_1510_);
v_fileName_1512_ = lean_ctor_get(v_a_1507_, 0);
v_options_1513_ = lean_ctor_get(v_a_1507_, 2);
v_currNamespace_1514_ = lean_ctor_get(v_a_1507_, 6);
v_openDecls_1515_ = lean_ctor_get(v_a_1507_, 7);
v___x_1516_ = lean_string_utf8_byte_size(v_docComment_1502_);
lean_inc_ref_n(v_docComment_1502_, 2);
v___x_1517_ = l_Lean_FileMap_ofString(v_docComment_1502_);
lean_inc_ref(v___x_1517_);
lean_inc_ref(v_fileName_1512_);
v___x_1518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1518_, 0, v_docComment_1502_);
lean_ctor_set(v___x_1518_, 1, v_fileName_1512_);
lean_ctor_set(v___x_1518_, 2, v___x_1517_);
lean_ctor_set(v___x_1518_, 3, v___x_1516_);
lean_inc(v_openDecls_1515_);
lean_inc(v_currNamespace_1514_);
lean_inc_ref(v_options_1513_);
v___x_1519_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1519_, 0, v_env_1511_);
lean_ctor_set(v___x_1519_, 1, v_options_1513_);
lean_ctor_set(v___x_1519_, 2, v_currNamespace_1514_);
lean_ctor_set(v___x_1519_, 3, v_openDecls_1515_);
v___x_1520_ = l_Lean_Parser_mkParserState(v_docComment_1502_);
lean_dec_ref(v_docComment_1502_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1523_ = l_Lean_Parser_getTokenTable(v_env_1511_);
v___x_1524_ = l_Lean_Parser_ParserFn_run(v___x_1522_, v___x_1518_, v___x_1519_, v___x_1523_, v___x_1520_);
lean_inc_ref(v___x_1524_);
v___x_1525_ = l_Lean_Parser_ParserState_allErrors(v___x_1524_);
v___x_1526_ = lean_array_get_size(v___x_1525_);
v___x_1527_ = lean_nat_dec_eq(v___x_1526_, v___x_1521_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; size_t v_sz_1529_; size_t v___x_1530_; lean_object* v___x_1531_; 
lean_dec_ref(v___x_1524_);
lean_dec_ref(v___x_1517_);
lean_dec(v_binders_1501_);
lean_dec(v_declName_1500_);
v___x_1528_ = lean_box(0);
v_sz_1529_ = lean_array_size(v___x_1525_);
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1525_, v_sz_1529_, v___x_1530_, v___x_1528_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec_ref(v___x_1525_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v___x_1531_, 0);
lean_dec(v_unused_1540_);
v___x_1533_ = v___x_1531_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v___x_1531_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1531_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1531_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_stxStack_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec_ref(v___x_1525_);
v_stxStack_1549_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_stxStack_1549_);
lean_dec_ref(v___x_1524_);
v___x_1550_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1549_);
lean_dec_ref(v_stxStack_1549_);
v___x_1551_ = l_Lean_Syntax_getArgs(v___x_1550_);
lean_dec(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1517_);
v___x_1553_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1500_, v_binders_1501_, v___x_1551_, v___x_1552_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1554_, lean_object* v_binders_1555_, lean_object* v_docComment_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_versoDocStringOfText(v_declName_1554_, v_binders_1555_, v_docComment_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1565_, uint8_t v_severity_1566_, uint8_t v_isSilent_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1565_, v_severity_1566_, v_isSilent_1567_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1576_, lean_object* v_severity_1577_, lean_object* v_isSilent_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
uint8_t v_severity_boxed_1586_; uint8_t v_isSilent_boxed_1587_; lean_object* v_res_1588_; 
v_severity_boxed_1586_ = lean_unbox(v_severity_1577_);
v_isSilent_boxed_1587_ = lean_unbox(v_isSilent_1578_);
v_res_1588_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1576_, v_severity_boxed_1586_, v_isSilent_boxed_1587_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_1589_, size_t v_i_1590_, lean_object* v_bs_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_usize_dec_lt(v_i_1590_, v_sz_1589_);
if (v___x_1592_ == 0)
{
return v_bs_1591_;
}
else
{
lean_object* v_v_1593_; lean_object* v___x_1594_; lean_object* v_bs_x27_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v_v_1593_ = lean_array_uget(v_bs_1591_, v_i_1590_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v_bs_x27_1595_ = lean_array_uset(v_bs_1591_, v_i_1590_, v___x_1594_);
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1590_, v___x_1596_);
v___x_1598_ = lean_array_uset(v_bs_x27_1595_, v_i_1590_, v_v_1593_);
v_i_1590_ = v___x_1597_;
v_bs_1591_ = v___x_1598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_){
_start:
{
size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_1603_, v_i_boxed_1604_, v_bs_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v___x_1606_, uint8_t v_suppressElabErrors_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 1)
{
lean_object* v_pre_1609_; 
v_pre_1609_ = lean_ctor_get(v_x_1608_, 0);
switch(lean_obj_tag(v_pre_1609_))
{
case 1:
{
lean_object* v_pre_1610_; 
v_pre_1610_ = lean_ctor_get(v_pre_1609_, 0);
switch(lean_obj_tag(v_pre_1610_))
{
case 0:
{
lean_object* v_str_1611_; lean_object* v_str_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_str_1611_ = lean_ctor_get(v_x_1608_, 1);
v_str_1612_ = lean_ctor_get(v_pre_1609_, 1);
v___x_1613_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1614_ = lean_string_dec_eq(v_str_1612_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1616_ = lean_string_dec_eq(v_str_1612_, v___x_1615_);
if (v___x_1616_ == 0)
{
return v___x_1606_;
}
else
{
lean_object* v___x_1617_; uint8_t v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1618_ = lean_string_dec_eq(v_str_1611_, v___x_1617_);
if (v___x_1618_ == 0)
{
return v___x_1606_;
}
else
{
return v_suppressElabErrors_1607_;
}
}
}
else
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1620_ = lean_string_dec_eq(v_str_1611_, v___x_1619_);
if (v___x_1620_ == 0)
{
return v___x_1606_;
}
else
{
return v_suppressElabErrors_1607_;
}
}
}
case 1:
{
lean_object* v_pre_1621_; 
v_pre_1621_ = lean_ctor_get(v_pre_1610_, 0);
if (lean_obj_tag(v_pre_1621_) == 0)
{
lean_object* v_str_1622_; lean_object* v_str_1623_; lean_object* v_str_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v_str_1622_ = lean_ctor_get(v_x_1608_, 1);
v_str_1623_ = lean_ctor_get(v_pre_1609_, 1);
v_str_1624_ = lean_ctor_get(v_pre_1610_, 1);
v___x_1625_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1626_ = lean_string_dec_eq(v_str_1624_, v___x_1625_);
if (v___x_1626_ == 0)
{
return v___x_1606_;
}
else
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1628_ = lean_string_dec_eq(v_str_1623_, v___x_1627_);
if (v___x_1628_ == 0)
{
return v___x_1606_;
}
else
{
lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1630_ = lean_string_dec_eq(v_str_1622_, v___x_1629_);
if (v___x_1630_ == 0)
{
return v___x_1606_;
}
else
{
return v_suppressElabErrors_1607_;
}
}
}
}
else
{
return v___x_1606_;
}
}
default: 
{
return v___x_1606_;
}
}
}
case 0:
{
lean_object* v_str_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_str_1631_ = lean_ctor_get(v_x_1608_, 1);
v___x_1632_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1633_ = lean_string_dec_eq(v_str_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
return v___x_1606_;
}
else
{
return v_suppressElabErrors_1607_;
}
}
default: 
{
return v___x_1606_;
}
}
}
else
{
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v___x_1634_, lean_object* v_suppressElabErrors_1635_, lean_object* v_x_1636_){
_start:
{
uint8_t v___x_11084__boxed_1637_; uint8_t v_suppressElabErrors_boxed_1638_; uint8_t v_res_1639_; lean_object* v_r_1640_; 
v___x_11084__boxed_1637_ = lean_unbox(v___x_1634_);
v_suppressElabErrors_boxed_1638_ = lean_unbox(v_suppressElabErrors_1635_);
v_res_1639_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v___x_11084__boxed_1637_, v_suppressElabErrors_boxed_1638_, v_x_1636_);
lean_dec(v_x_1636_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v___x_1641_, uint8_t v_suppressElabErrors_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 1)
{
lean_object* v_pre_1644_; 
v_pre_1644_ = lean_ctor_get(v_x_1643_, 0);
switch(lean_obj_tag(v_pre_1644_))
{
case 1:
{
lean_object* v_pre_1645_; 
v_pre_1645_ = lean_ctor_get(v_pre_1644_, 0);
switch(lean_obj_tag(v_pre_1645_))
{
case 0:
{
lean_object* v_str_1646_; lean_object* v_str_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_str_1646_ = lean_ctor_get(v_x_1643_, 1);
v_str_1647_ = lean_ctor_get(v_pre_1644_, 1);
v___x_1648_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1649_ = lean_string_dec_eq(v_str_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1651_ = lean_string_dec_eq(v_str_1647_, v___x_1650_);
if (v___x_1651_ == 0)
{
return v___x_1641_;
}
else
{
lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1653_ = lean_string_dec_eq(v_str_1646_, v___x_1652_);
if (v___x_1653_ == 0)
{
return v___x_1641_;
}
else
{
return v_suppressElabErrors_1642_;
}
}
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1655_ = lean_string_dec_eq(v_str_1646_, v___x_1654_);
if (v___x_1655_ == 0)
{
return v___x_1641_;
}
else
{
return v_suppressElabErrors_1642_;
}
}
}
case 1:
{
lean_object* v_pre_1656_; 
v_pre_1656_ = lean_ctor_get(v_pre_1645_, 0);
if (lean_obj_tag(v_pre_1656_) == 0)
{
lean_object* v_str_1657_; lean_object* v_str_1658_; lean_object* v_str_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_str_1657_ = lean_ctor_get(v_x_1643_, 1);
v_str_1658_ = lean_ctor_get(v_pre_1644_, 1);
v_str_1659_ = lean_ctor_get(v_pre_1645_, 1);
v___x_1660_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1661_ = lean_string_dec_eq(v_str_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
return v___x_1641_;
}
else
{
lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1662_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1663_ = lean_string_dec_eq(v_str_1658_, v___x_1662_);
if (v___x_1663_ == 0)
{
return v___x_1641_;
}
else
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1665_ = lean_string_dec_eq(v_str_1657_, v___x_1664_);
if (v___x_1665_ == 0)
{
return v___x_1641_;
}
else
{
return v_suppressElabErrors_1642_;
}
}
}
}
else
{
return v___x_1641_;
}
}
default: 
{
return v___x_1641_;
}
}
}
case 0:
{
lean_object* v_str_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_str_1666_ = lean_ctor_get(v_x_1643_, 1);
v___x_1667_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1668_ = lean_string_dec_eq(v_str_1666_, v___x_1667_);
if (v___x_1668_ == 0)
{
return v___x_1641_;
}
else
{
return v_suppressElabErrors_1642_;
}
}
default: 
{
return v___x_1641_;
}
}
}
else
{
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v___x_1669_, lean_object* v_suppressElabErrors_1670_, lean_object* v_x_1671_){
_start:
{
uint8_t v___x_11148__boxed_1672_; uint8_t v_suppressElabErrors_boxed_1673_; uint8_t v_res_1674_; lean_object* v_r_1675_; 
v___x_11148__boxed_1672_ = lean_unbox(v___x_1669_);
v_suppressElabErrors_boxed_1673_ = lean_unbox(v_suppressElabErrors_1670_);
v_res_1674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v___x_11148__boxed_1672_, v_suppressElabErrors_boxed_1673_, v_x_1671_);
lean_dec(v_x_1671_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_1676_, lean_object* v___x_1677_, lean_object* v_as_1678_, size_t v_sz_1679_, size_t v_i_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_a_1686_; uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1680_, v_sz_1679_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref(v___x_1676_);
v___x_1691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1691_, 0, v_b_1681_);
return v___x_1691_;
}
else
{
lean_object* v_a_1692_; lean_object* v_snd_1693_; lean_object* v_fst_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1751_; 
v_a_1692_ = lean_array_uget(v_as_1678_, v_i_1680_);
v_snd_1693_ = lean_ctor_get(v_a_1692_, 1);
v_fst_1694_ = lean_ctor_get(v_a_1692_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1692_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1696_ = v_a_1692_;
v_isShared_1697_ = v_isSharedCheck_1751_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snd_1693_);
lean_inc(v_fst_1694_);
lean_dec(v_a_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1751_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1749_; 
v_snd_1698_ = lean_ctor_get(v_snd_1693_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_snd_1693_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v_snd_1693_, 0);
lean_dec(v_unused_1750_);
v___x_1700_ = v_snd_1693_;
v_isShared_1701_ = v_isSharedCheck_1749_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_dec(v_snd_1693_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1749_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_fileName_1702_; uint8_t v_suppressElabErrors_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___y_1715_; lean_object* v___y_1716_; 
v_fileName_1702_ = lean_ctor_get(v___y_1682_, 0);
v_suppressElabErrors_1703_ = lean_ctor_get_uint8(v___y_1682_, sizeof(void*)*14 + 1);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = lean_nat_dec_eq(v___x_1677_, v___x_1705_);
lean_inc_ref(v___x_1676_);
v___x_1707_ = l_Lean_FileMap_toPosition(v___x_1676_, v_fst_1694_);
lean_dec(v_fst_1694_);
v___x_1708_ = lean_box(0);
v___x_1709_ = 2;
v___x_1710_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1711_ = l_Lean_Parser_Error_toString(v_snd_1698_);
v___x_1712_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1711_);
v___x_1713_ = l_Lean_MessageData_ofFormat(v___x_1712_);
if (v_suppressElabErrors_1703_ == 0)
{
v___y_1715_ = v___y_1682_;
v___y_1716_ = v___y_1683_;
goto v___jp_1714_;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___f_1747_; uint8_t v___x_1748_; 
v___x_1745_ = lean_box(v___x_1706_);
v___x_1746_ = lean_box(v_suppressElabErrors_1703_);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1747_, 0, v___x_1745_);
lean_closure_set(v___f_1747_, 1, v___x_1746_);
lean_inc_ref(v___x_1713_);
v___x_1748_ = l_Lean_MessageData_hasTag(v___f_1747_, v___x_1713_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v___x_1713_);
lean_dec_ref(v___x_1707_);
lean_del_object(v___x_1700_);
lean_del_object(v___x_1696_);
v_a_1686_ = v___x_1704_;
goto v___jp_1685_;
}
else
{
v___y_1715_ = v___y_1682_;
v___y_1716_ = v___y_1683_;
goto v___jp_1714_;
}
}
v___jp_1714_:
{
lean_object* v___x_1717_; lean_object* v_currNamespace_1718_; lean_object* v_openDecls_1719_; lean_object* v___x_1721_; 
v___x_1717_ = lean_st_ref_take(v___y_1716_);
v_currNamespace_1718_ = lean_ctor_get(v___y_1715_, 6);
v_openDecls_1719_ = lean_ctor_get(v___y_1715_, 7);
lean_inc(v_openDecls_1719_);
lean_inc(v_currNamespace_1718_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_openDecls_1719_);
lean_ctor_set(v___x_1700_, 0, v_currNamespace_1718_);
v___x_1721_ = v___x_1700_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_currNamespace_1718_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_openDecls_1719_);
v___x_1721_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 4);
lean_ctor_set(v___x_1696_, 1, v___x_1713_);
lean_ctor_set(v___x_1696_, 0, v___x_1721_);
v___x_1723_ = v___x_1696_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1713_);
v___x_1723_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v_nextMacroScope_1726_; lean_object* v_ngen_1727_; lean_object* v_auxDeclNGen_1728_; lean_object* v_traceState_1729_; lean_object* v_cache_1730_; lean_object* v_messages_1731_; lean_object* v_infoState_1732_; lean_object* v_snapshotTasks_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1742_; 
lean_inc_ref(v_fileName_1702_);
v___x_1724_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1724_, 0, v_fileName_1702_);
lean_ctor_set(v___x_1724_, 1, v___x_1707_);
lean_ctor_set(v___x_1724_, 2, v___x_1708_);
lean_ctor_set(v___x_1724_, 3, v___x_1710_);
lean_ctor_set(v___x_1724_, 4, v___x_1723_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5, v___x_1706_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5 + 1, v___x_1709_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5 + 2, v___x_1706_);
v_env_1725_ = lean_ctor_get(v___x_1717_, 0);
v_nextMacroScope_1726_ = lean_ctor_get(v___x_1717_, 1);
v_ngen_1727_ = lean_ctor_get(v___x_1717_, 2);
v_auxDeclNGen_1728_ = lean_ctor_get(v___x_1717_, 3);
v_traceState_1729_ = lean_ctor_get(v___x_1717_, 4);
v_cache_1730_ = lean_ctor_get(v___x_1717_, 5);
v_messages_1731_ = lean_ctor_get(v___x_1717_, 6);
v_infoState_1732_ = lean_ctor_get(v___x_1717_, 7);
v_snapshotTasks_1733_ = lean_ctor_get(v___x_1717_, 8);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1735_ = v___x_1717_;
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_snapshotTasks_1733_);
lean_inc(v_infoState_1732_);
lean_inc(v_messages_1731_);
lean_inc(v_cache_1730_);
lean_inc(v_traceState_1729_);
lean_inc(v_auxDeclNGen_1728_);
lean_inc(v_ngen_1727_);
lean_inc(v_nextMacroScope_1726_);
lean_inc(v_env_1725_);
lean_dec(v___x_1717_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1742_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = l_Lean_MessageLog_add(v___x_1724_, v_messages_1731_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 6, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_env_1725_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_nextMacroScope_1726_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_ngen_1727_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_auxDeclNGen_1728_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_traceState_1729_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_cache_1730_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_infoState_1732_);
lean_ctor_set(v_reuseFailAlloc_1741_, 8, v_snapshotTasks_1733_);
v___x_1739_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_st_ref_set(v___y_1716_, v___x_1739_);
v_a_1686_ = v___x_1704_;
goto v___jp_1685_;
}
}
}
}
}
}
}
}
v___jp_1685_:
{
size_t v___x_1687_; size_t v___x_1688_; 
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1680_, v___x_1687_);
v_i_1680_ = v___x_1688_;
v_b_1681_ = v_a_1686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1752_, lean_object* v___x_1753_, lean_object* v_as_1754_, lean_object* v_sz_1755_, lean_object* v_i_1756_, lean_object* v_b_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_sz_boxed_1761_; size_t v_i_boxed_1762_; lean_object* v_res_1763_; 
v_sz_boxed_1761_ = lean_unbox_usize(v_sz_1755_);
lean_dec(v_sz_1755_);
v_i_boxed_1762_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1752_, v___x_1753_, v_as_1754_, v_sz_boxed_1761_, v_i_boxed_1762_, v_b_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_as_1754_);
lean_dec(v___x_1753_);
return v_res_1763_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = lean_box(1);
v___x_1765_ = l_Lean_MessageData_ofFormat(v___x_1764_);
return v___x_1765_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1770_ = l_Lean_MessageData_ofFormat(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
if (lean_obj_tag(v_x_1772_) == 0)
{
return v_x_1771_;
}
else
{
lean_object* v_head_1773_; lean_object* v_tail_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1796_; 
v_head_1773_ = lean_ctor_get(v_x_1772_, 0);
v_tail_1774_ = lean_ctor_get(v_x_1772_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_x_1772_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1776_ = v_x_1772_;
v_isShared_1777_ = v_isSharedCheck_1796_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_tail_1774_);
lean_inc(v_head_1773_);
lean_dec(v_x_1772_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1796_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_before_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1794_; 
v_before_1778_ = lean_ctor_get(v_head_1773_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_head_1773_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_head_1773_, 1);
lean_dec(v_unused_1795_);
v___x_1780_ = v_head_1773_;
v_isShared_1781_ = v_isSharedCheck_1794_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_before_1778_);
lean_dec(v_head_1773_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1794_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 7);
lean_ctor_set(v___x_1780_, 1, v___x_1782_);
lean_ctor_set(v___x_1780_, 0, v_x_1771_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_x_1771_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1777_ == 0)
{
lean_ctor_set_tag(v___x_1776_, 7);
lean_ctor_set(v___x_1776_, 1, v___x_1785_);
lean_ctor_set(v___x_1776_, 0, v___x_1784_);
v___x_1787_ = v___x_1776_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1788_ = l_Lean_MessageData_ofSyntax(v_before_1778_);
v___x_1789_ = l_Lean_indentD(v___x_1788_);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1787_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v_x_1771_ = v___x_1790_;
v_x_1772_ = v_tail_1774_;
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
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1801_ = l_Lean_MessageData_ofFormat(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1802_, lean_object* v_macroStack_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_options_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_options_1806_ = lean_ctor_get(v___y_1804_, 2);
v___x_1807_ = l_Lean_Elab_pp_macroStack;
v___x_1808_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec(v_macroStack_1803_);
v___x_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_msgData_1802_);
return v___x_1809_;
}
else
{
if (lean_obj_tag(v_macroStack_1803_) == 0)
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_msgData_1802_);
return v___x_1810_;
}
else
{
lean_object* v_head_1811_; lean_object* v_after_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1827_; 
v_head_1811_ = lean_ctor_get(v_macroStack_1803_, 0);
lean_inc(v_head_1811_);
v_after_1812_ = lean_ctor_get(v_head_1811_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_head_1811_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_head_1811_, 0);
lean_dec(v_unused_1828_);
v___x_1814_ = v_head_1811_;
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_after_1812_);
lean_dec(v_head_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1827_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v___x_1816_);
lean_ctor_set(v___x_1814_, 0, v_msgData_1802_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_msgData_1802_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_msgData_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1819_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1818_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = l_Lean_MessageData_ofSyntax(v_after_1812_);
v___x_1822_ = l_Lean_indentD(v___x_1821_);
v_msgData_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1823_, 0, v___x_1820_);
lean_ctor_set(v_msgData_1823_, 1, v___x_1822_);
v___x_1824_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1823_, v_macroStack_1803_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1829_, lean_object* v_macroStack_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1829_, v_macroStack_1830_, v___y_1831_);
lean_dec_ref(v___y_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_ref_1842_; lean_object* v___x_1843_; lean_object* v_a_1844_; lean_object* v_macroStack_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_ref_1842_ = lean_ctor_get(v___y_1839_, 5);
v___x_1843_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1834_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v_macroStack_1845_ = lean_ctor_get(v___y_1835_, 1);
v___x_1846_ = l_Lean_Elab_getBetterRef(v_ref_1842_, v_macroStack_1845_);
lean_inc(v_macroStack_1845_);
v___x_1847_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1844_, v_macroStack_1845_, v___y_1839_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1846_);
lean_ctor_set(v___x_1852_, 1, v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set_tag(v___x_1850_, 1);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1866_, lean_object* v_msg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_fileName_1875_; lean_object* v_fileMap_1876_; lean_object* v_options_1877_; lean_object* v_currRecDepth_1878_; lean_object* v_maxRecDepth_1879_; lean_object* v_ref_1880_; lean_object* v_currNamespace_1881_; lean_object* v_openDecls_1882_; lean_object* v_initHeartbeats_1883_; lean_object* v_maxHeartbeats_1884_; lean_object* v_quotContext_1885_; lean_object* v_currMacroScope_1886_; uint8_t v_diag_1887_; lean_object* v_cancelTk_x3f_1888_; uint8_t v_suppressElabErrors_1889_; lean_object* v_inheritedTraceOptions_1890_; lean_object* v_ref_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_fileName_1875_ = lean_ctor_get(v___y_1872_, 0);
v_fileMap_1876_ = lean_ctor_get(v___y_1872_, 1);
v_options_1877_ = lean_ctor_get(v___y_1872_, 2);
v_currRecDepth_1878_ = lean_ctor_get(v___y_1872_, 3);
v_maxRecDepth_1879_ = lean_ctor_get(v___y_1872_, 4);
v_ref_1880_ = lean_ctor_get(v___y_1872_, 5);
v_currNamespace_1881_ = lean_ctor_get(v___y_1872_, 6);
v_openDecls_1882_ = lean_ctor_get(v___y_1872_, 7);
v_initHeartbeats_1883_ = lean_ctor_get(v___y_1872_, 8);
v_maxHeartbeats_1884_ = lean_ctor_get(v___y_1872_, 9);
v_quotContext_1885_ = lean_ctor_get(v___y_1872_, 10);
v_currMacroScope_1886_ = lean_ctor_get(v___y_1872_, 11);
v_diag_1887_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14);
v_cancelTk_x3f_1888_ = lean_ctor_get(v___y_1872_, 12);
v_suppressElabErrors_1889_ = lean_ctor_get_uint8(v___y_1872_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1890_ = lean_ctor_get(v___y_1872_, 13);
v_ref_1891_ = l_Lean_replaceRef(v_ref_1866_, v_ref_1880_);
lean_inc_ref(v_inheritedTraceOptions_1890_);
lean_inc(v_cancelTk_x3f_1888_);
lean_inc(v_currMacroScope_1886_);
lean_inc(v_quotContext_1885_);
lean_inc(v_maxHeartbeats_1884_);
lean_inc(v_initHeartbeats_1883_);
lean_inc(v_openDecls_1882_);
lean_inc(v_currNamespace_1881_);
lean_inc(v_maxRecDepth_1879_);
lean_inc(v_currRecDepth_1878_);
lean_inc_ref(v_options_1877_);
lean_inc_ref(v_fileMap_1876_);
lean_inc_ref(v_fileName_1875_);
v___x_1892_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1892_, 0, v_fileName_1875_);
lean_ctor_set(v___x_1892_, 1, v_fileMap_1876_);
lean_ctor_set(v___x_1892_, 2, v_options_1877_);
lean_ctor_set(v___x_1892_, 3, v_currRecDepth_1878_);
lean_ctor_set(v___x_1892_, 4, v_maxRecDepth_1879_);
lean_ctor_set(v___x_1892_, 5, v_ref_1891_);
lean_ctor_set(v___x_1892_, 6, v_currNamespace_1881_);
lean_ctor_set(v___x_1892_, 7, v_openDecls_1882_);
lean_ctor_set(v___x_1892_, 8, v_initHeartbeats_1883_);
lean_ctor_set(v___x_1892_, 9, v_maxHeartbeats_1884_);
lean_ctor_set(v___x_1892_, 10, v_quotContext_1885_);
lean_ctor_set(v___x_1892_, 11, v_currMacroScope_1886_);
lean_ctor_set(v___x_1892_, 12, v_cancelTk_x3f_1888_);
lean_ctor_set(v___x_1892_, 13, v_inheritedTraceOptions_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14, v_diag_1887_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*14 + 1, v_suppressElabErrors_1889_);
v___x_1893_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___x_1892_, v___y_1873_);
lean_dec_ref_known(v___x_1892_, 14);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1894_, lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1894_, v_msg_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_ref_1894_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; uint8_t v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
lean_inc(v_docComment_1904_);
v___x_2077_ = l_Lean_Syntax_getKind(v_docComment_1904_);
v___x_2078_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2079_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2080_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2081_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2082_ = lean_name_eq(v___x_2077_, v___x_2081_);
lean_dec(v___x_2077_);
if (v___x_2082_ == 0)
{
goto v___jp_2054_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = l_Lean_Syntax_getArg(v_docComment_1904_, v___x_2083_);
if (lean_obj_tag(v___x_2084_) == 1)
{
lean_object* v_kind_2085_; 
v_kind_2085_ = lean_ctor_get(v___x_2084_, 1);
lean_inc(v_kind_2085_);
if (lean_obj_tag(v_kind_2085_) == 1)
{
lean_object* v_pre_2086_; 
v_pre_2086_ = lean_ctor_get(v_kind_2085_, 0);
lean_inc(v_pre_2086_);
if (lean_obj_tag(v_pre_2086_) == 1)
{
lean_object* v_pre_2087_; 
v_pre_2087_ = lean_ctor_get(v_pre_2086_, 0);
lean_inc(v_pre_2087_);
if (lean_obj_tag(v_pre_2087_) == 1)
{
lean_object* v_pre_2088_; 
v_pre_2088_ = lean_ctor_get(v_pre_2087_, 0);
lean_inc(v_pre_2088_);
if (lean_obj_tag(v_pre_2088_) == 1)
{
lean_object* v_pre_2089_; 
v_pre_2089_ = lean_ctor_get(v_pre_2088_, 0);
lean_inc(v_pre_2089_);
if (lean_obj_tag(v_pre_2089_) == 0)
{
lean_object* v_info_2090_; lean_object* v_args_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2117_; 
v_info_2090_ = lean_ctor_get(v___x_2084_, 0);
v_args_2091_ = lean_ctor_get(v___x_2084_, 2);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2084_, 1);
lean_dec(v_unused_2118_);
v___x_2093_ = v___x_2084_;
v_isShared_2094_ = v_isSharedCheck_2117_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_args_2091_);
lean_inc(v_info_2090_);
lean_dec(v___x_2084_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2117_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_str_2095_; lean_object* v_str_2096_; lean_object* v_str_2097_; lean_object* v_str_2098_; uint8_t v___x_2099_; 
v_str_2095_ = lean_ctor_get(v_kind_2085_, 1);
lean_inc_ref(v_str_2095_);
lean_dec_ref_known(v_kind_2085_, 2);
v_str_2096_ = lean_ctor_get(v_pre_2086_, 1);
lean_inc_ref(v_str_2096_);
lean_dec_ref_known(v_pre_2086_, 2);
v_str_2097_ = lean_ctor_get(v_pre_2087_, 1);
lean_inc_ref(v_str_2097_);
lean_dec_ref_known(v_pre_2087_, 2);
v_str_2098_ = lean_ctor_get(v_pre_2088_, 1);
lean_inc_ref(v_str_2098_);
lean_dec_ref_known(v_pre_2088_, 2);
v___x_2099_ = lean_string_dec_eq(v_str_2098_, v___x_2078_);
lean_dec_ref(v_str_2098_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v_str_2097_);
lean_dec_ref(v_str_2096_);
lean_dec_ref(v_str_2095_);
lean_del_object(v___x_2093_);
lean_dec_ref(v_args_2091_);
lean_dec(v_info_2090_);
goto v___jp_2054_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_string_dec_eq(v_str_2097_, v___x_2079_);
lean_dec_ref(v_str_2097_);
if (v___x_2100_ == 0)
{
lean_dec_ref(v_str_2096_);
lean_dec_ref(v_str_2095_);
lean_del_object(v___x_2093_);
lean_dec_ref(v_args_2091_);
lean_dec(v_info_2090_);
goto v___jp_2054_;
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_string_dec_eq(v_str_2096_, v___x_2080_);
lean_dec_ref(v_str_2096_);
if (v___x_2101_ == 0)
{
lean_dec_ref(v_str_2095_);
lean_del_object(v___x_2093_);
lean_dec_ref(v_args_2091_);
lean_dec(v_info_2090_);
goto v___jp_2054_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2103_ = lean_string_dec_eq(v_str_2095_, v___x_2102_);
lean_dec_ref(v_str_2095_);
if (v___x_2103_ == 0)
{
lean_del_object(v___x_2093_);
lean_dec_ref(v_args_2091_);
lean_dec(v_info_2090_);
goto v___jp_2054_;
}
else
{
lean_dec(v_docComment_1904_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2093_);
lean_dec_ref(v_args_2091_);
lean_dec(v_info_2090_);
v___x_2104_ = lean_box(0);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2106_ = l_Lean_Name_str___override(v_pre_2089_, v___x_2078_);
v___x_2107_ = l_Lean_Name_str___override(v___x_2106_, v___x_2079_);
v___x_2108_ = l_Lean_Name_str___override(v___x_2107_, v___x_2080_);
v___x_2109_ = l_Lean_Name_str___override(v___x_2108_, v___x_2102_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2109_);
v___x_2111_ = v___x_2093_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_info_2090_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_args_2091_);
v___x_2111_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = lean_unsigned_to_nat(1u);
v___x_2113_ = l_Lean_Syntax_getArg(v___x_2111_, v___x_2112_);
lean_dec_ref(v___x_2111_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
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
lean_dec(v_pre_2089_);
lean_dec_ref_known(v_pre_2088_, 2);
lean_dec_ref_known(v_pre_2087_, 2);
lean_dec_ref_known(v_pre_2086_, 2);
lean_dec_ref_known(v_kind_2085_, 2);
lean_dec_ref_known(v___x_2084_, 3);
goto v___jp_2054_;
}
}
else
{
lean_dec_ref_known(v_pre_2087_, 2);
lean_dec(v_pre_2088_);
lean_dec_ref_known(v_pre_2086_, 2);
lean_dec_ref_known(v_kind_2085_, 2);
lean_dec_ref_known(v___x_2084_, 3);
goto v___jp_2054_;
}
}
else
{
lean_dec_ref_known(v_pre_2086_, 2);
lean_dec(v_pre_2087_);
lean_dec_ref_known(v_kind_2085_, 2);
lean_dec_ref_known(v___x_2084_, 3);
goto v___jp_2054_;
}
}
else
{
lean_dec(v_pre_2086_);
lean_dec_ref_known(v_kind_2085_, 2);
lean_dec_ref_known(v___x_2084_, 3);
goto v___jp_2054_;
}
}
else
{
lean_dec_ref_known(v___x_2084_, 3);
lean_dec(v_kind_2085_);
goto v___jp_2054_;
}
}
else
{
lean_dec(v___x_2084_);
goto v___jp_2054_;
}
}
v___jp_1912_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
return v___x_1914_;
}
v___jp_1915_:
{
lean_object* v___x_1925_; lean_object* v_currNamespace_1926_; lean_object* v_openDecls_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_env_1931_; lean_object* v_nextMacroScope_1932_; lean_object* v_ngen_1933_; lean_object* v_auxDeclNGen_1934_; lean_object* v_traceState_1935_; lean_object* v_cache_1936_; lean_object* v_messages_1937_; lean_object* v_infoState_1938_; lean_object* v_snapshotTasks_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1948_; 
v___x_1925_ = lean_st_ref_take(v___y_1924_);
v_currNamespace_1926_ = lean_ctor_get(v___y_1923_, 6);
v_openDecls_1927_ = lean_ctor_get(v___y_1923_, 7);
lean_inc(v_openDecls_1927_);
lean_inc(v_currNamespace_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_currNamespace_1926_);
lean_ctor_set(v___x_1928_, 1, v_openDecls_1927_);
v___x_1929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v___y_1919_);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1918_);
v___x_1930_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1930_, 0, v___y_1918_);
lean_ctor_set(v___x_1930_, 1, v___y_1921_);
lean_ctor_set(v___x_1930_, 2, v___y_1917_);
lean_ctor_set(v___x_1930_, 3, v___y_1920_);
lean_ctor_set(v___x_1930_, 4, v___x_1929_);
lean_ctor_set_uint8(v___x_1930_, sizeof(void*)*5, v___y_1922_);
lean_ctor_set_uint8(v___x_1930_, sizeof(void*)*5 + 1, v___y_1916_);
lean_ctor_set_uint8(v___x_1930_, sizeof(void*)*5 + 2, v___y_1922_);
v_env_1931_ = lean_ctor_get(v___x_1925_, 0);
v_nextMacroScope_1932_ = lean_ctor_get(v___x_1925_, 1);
v_ngen_1933_ = lean_ctor_get(v___x_1925_, 2);
v_auxDeclNGen_1934_ = lean_ctor_get(v___x_1925_, 3);
v_traceState_1935_ = lean_ctor_get(v___x_1925_, 4);
v_cache_1936_ = lean_ctor_get(v___x_1925_, 5);
v_messages_1937_ = lean_ctor_get(v___x_1925_, 6);
v_infoState_1938_ = lean_ctor_get(v___x_1925_, 7);
v_snapshotTasks_1939_ = lean_ctor_get(v___x_1925_, 8);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1941_ = v___x_1925_;
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_snapshotTasks_1939_);
lean_inc(v_infoState_1938_);
lean_inc(v_messages_1937_);
lean_inc(v_cache_1936_);
lean_inc(v_traceState_1935_);
lean_inc(v_auxDeclNGen_1934_);
lean_inc(v_ngen_1933_);
lean_inc(v_nextMacroScope_1932_);
lean_inc(v_env_1931_);
lean_dec(v___x_1925_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = l_Lean_MessageLog_add(v___x_1930_, v_messages_1937_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 6, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_env_1931_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_nextMacroScope_1932_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_ngen_1933_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_auxDeclNGen_1934_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_traceState_1935_);
lean_ctor_set(v_reuseFailAlloc_1947_, 5, v_cache_1936_);
lean_ctor_set(v_reuseFailAlloc_1947_, 6, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1947_, 7, v_infoState_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 8, v_snapshotTasks_1939_);
v___x_1945_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_st_ref_set(v___y_1924_, v___x_1945_);
goto v___jp_1912_;
}
}
}
v___jp_1949_:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
lean_inc_ref(v___y_1956_);
v___x_1957_ = l_Lean_Parser_ParserState_allErrors(v___y_1956_);
v___x_1958_ = lean_array_get_size(v___x_1957_);
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_nat_dec_eq(v___x_1958_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v___y_1956_);
lean_dec_ref(v___y_1955_);
v___x_1961_ = lean_box(0);
v_sz_1962_ = lean_array_size(v___x_1957_);
v___x_1963_ = ((size_t)0ULL);
lean_inc_ref(v___y_1951_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1951_, v___x_1958_, v___x_1957_, v_sz_1962_, v___x_1963_, v___x_1961_, v___y_1909_, v___y_1910_);
lean_dec_ref(v___x_1957_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_box(0);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1964_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1964_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
lean_object* v_stxStack_1982_; lean_object* v_pos_1983_; uint8_t v___x_1984_; 
lean_dec_ref(v___x_1957_);
v_stxStack_1982_ = lean_ctor_get(v___y_1956_, 0);
lean_inc_ref(v_stxStack_1982_);
v_pos_1983_ = lean_ctor_get(v___y_1956_, 2);
lean_inc(v_pos_1983_);
lean_dec_ref(v___y_1956_);
v___x_1984_ = l_Lean_Parser_InputContext_atEnd(v___y_1955_, v_pos_1983_);
lean_dec_ref(v___y_1955_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint32_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref(v_stxStack_1982_);
lean_inc_ref(v___y_1951_);
v___x_1985_ = l_Lean_FileMap_toPosition(v___y_1951_, v_pos_1983_);
v___x_1986_ = lean_box(0);
v___x_1987_ = 2;
v___x_1988_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1989_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1990_ = lean_string_utf8_get(v___y_1953_, v_pos_1983_);
lean_dec(v_pos_1983_);
v___x_1991_ = lean_string_push(v___x_1988_, v___x_1990_);
v___x_1992_ = lean_string_append(v___x_1989_, v___x_1991_);
lean_dec_ref(v___x_1991_);
v___x_1993_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1994_ = lean_string_append(v___x_1992_, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
v___x_1996_ = l_Lean_MessageData_ofFormat(v___x_1995_);
if (v___y_1954_ == 0)
{
v___y_1916_ = v___x_1987_;
v___y_1917_ = v___x_1986_;
v___y_1918_ = v___y_1952_;
v___y_1919_ = v___x_1996_;
v___y_1920_ = v___x_1988_;
v___y_1921_ = v___x_1985_;
v___y_1922_ = v___x_1984_;
v___y_1923_ = v___y_1909_;
v___y_1924_ = v___y_1910_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; uint8_t v___x_2000_; 
v___x_1997_ = lean_box(v___x_1984_);
v___x_1998_ = lean_box(v___y_1950_);
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1999_, 0, v___x_1997_);
lean_closure_set(v___f_1999_, 1, v___x_1998_);
lean_inc_ref(v___x_1996_);
v___x_2000_ = l_Lean_MessageData_hasTag(v___f_1999_, v___x_1996_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v___x_1985_);
goto v___jp_1912_;
}
else
{
v___y_1916_ = v___x_1987_;
v___y_1917_ = v___x_1986_;
v___y_1918_ = v___y_1952_;
v___y_1919_ = v___x_1996_;
v___y_1920_ = v___x_1988_;
v___y_1921_ = v___x_1985_;
v___y_1922_ = v___x_1984_;
v___y_1923_ = v___y_1909_;
v___y_1924_ = v___y_1910_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec(v_pos_1983_);
v___x_2001_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1982_);
lean_dec_ref(v_stxStack_1982_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
}
}
v___jp_2004_:
{
if (v___y_2016_ == 0)
{
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v___y_2006_);
v___y_1950_ = v___y_2005_;
v___y_1951_ = v___y_2007_;
v___y_1952_ = v___y_2008_;
v___y_1953_ = v___y_2010_;
v___y_1954_ = v___y_2015_;
v___y_1955_ = v___y_2014_;
v___y_1956_ = v___y_2011_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_pos_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___y_2013_);
lean_ctor_set(v___x_2020_, 1, v___x_2017_);
v___x_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2017_);
lean_ctor_set(v___x_2021_, 1, v___x_2018_);
lean_ctor_set(v___x_2021_, 2, v___x_2019_);
lean_ctor_set(v___x_2021_, 3, v___x_2020_);
lean_ctor_set(v___x_2021_, 4, v___x_2017_);
v_pos_2022_ = lean_ctor_get(v___y_2011_, 2);
lean_inc(v_pos_2022_);
lean_dec_ref(v___y_2011_);
v___x_2023_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_2023_, 0, v___x_2021_);
v___x_2024_ = l_Lean_Parser_ParserState_setPos(v___y_2006_, v_pos_2022_);
lean_inc_ref(v___y_2014_);
v___x_2025_ = l_Lean_Parser_ParserFn_run(v___x_2023_, v___y_2014_, v___y_2009_, v___y_2012_, v___x_2024_);
v___y_1950_ = v___y_2005_;
v___y_1951_ = v___y_2007_;
v___y_1952_ = v___y_2008_;
v___y_1953_ = v___y_2010_;
v___y_1954_ = v___y_2015_;
v___y_1955_ = v___y_2014_;
v___y_1956_ = v___x_2025_;
goto v___jp_1949_;
}
}
v___jp_2026_:
{
lean_object* v___x_2038_; lean_object* v_env_2039_; lean_object* v_ictx_2040_; lean_object* v_pmctx_2041_; lean_object* v_blockCtxt_2042_; lean_object* v___x_2043_; lean_object* v_s_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_s_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2038_ = lean_st_ref_get(v___y_1910_);
v_env_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc_ref_n(v_env_2039_, 2);
lean_dec(v___x_2038_);
lean_inc(v___y_2037_);
lean_inc_ref_n(v___y_2030_, 2);
lean_inc_ref(v___y_2031_);
lean_inc_ref(v___y_2027_);
v_ictx_2040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2040_, 0, v___y_2027_);
lean_ctor_set(v_ictx_2040_, 1, v___y_2031_);
lean_ctor_set(v_ictx_2040_, 2, v___y_2030_);
lean_ctor_set(v_ictx_2040_, 3, v___y_2037_);
lean_inc(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2029_);
v_pmctx_2041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2041_, 0, v_env_2039_);
lean_ctor_set(v_pmctx_2041_, 1, v___y_2029_);
lean_ctor_set(v_pmctx_2041_, 2, v___y_2033_);
lean_ctor_set(v_pmctx_2041_, 3, v___y_2034_);
lean_inc(v___y_2032_);
v_blockCtxt_2042_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_2030_, v___y_2032_, v___y_2037_);
v___x_2043_ = l_Lean_Parser_mkParserState(v___y_2027_);
lean_inc_ref(v___x_2043_);
v_s_2044_ = l_Lean_Parser_ParserState_setPos(v___x_2043_, v___y_2032_);
v___x_2045_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_2045_, 0, v_blockCtxt_2042_);
v___x_2046_ = l_Lean_Parser_getTokenTable(v_env_2039_);
lean_inc_ref(v___x_2046_);
lean_inc_ref(v_pmctx_2041_);
lean_inc_ref(v_ictx_2040_);
v_s_2047_ = l_Lean_Parser_ParserFn_run(v___x_2045_, v_ictx_2040_, v_pmctx_2041_, v___x_2046_, v_s_2044_);
lean_inc_ref(v_s_2047_);
v___x_2048_ = l_Lean_Parser_ParserState_allErrors(v_s_2047_);
v___x_2049_ = lean_array_get_size(v___x_2048_);
lean_dec_ref(v___x_2048_);
v___x_2050_ = lean_unsigned_to_nat(0u);
v___x_2051_ = lean_nat_dec_eq(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
v___y_2005_ = v___y_2028_;
v___y_2006_ = v___x_2043_;
v___y_2007_ = v___y_2030_;
v___y_2008_ = v___y_2031_;
v___y_2009_ = v_pmctx_2041_;
v___y_2010_ = v___y_2027_;
v___y_2011_ = v_s_2047_;
v___y_2012_ = v___x_2046_;
v___y_2013_ = v___y_2035_;
v___y_2014_ = v_ictx_2040_;
v___y_2015_ = v___y_2036_;
v___y_2016_ = v___x_2051_;
goto v___jp_2004_;
}
else
{
lean_object* v_pos_2052_; uint8_t v___x_2053_; 
v_pos_2052_ = lean_ctor_get(v_s_2047_, 2);
lean_inc(v_pos_2052_);
v___x_2053_ = l_Lean_Parser_InputContext_atEnd(v_ictx_2040_, v_pos_2052_);
lean_dec(v_pos_2052_);
if (v___x_2053_ == 0)
{
v___y_2005_ = v___y_2028_;
v___y_2006_ = v___x_2043_;
v___y_2007_ = v___y_2030_;
v___y_2008_ = v___y_2031_;
v___y_2009_ = v_pmctx_2041_;
v___y_2010_ = v___y_2027_;
v___y_2011_ = v_s_2047_;
v___y_2012_ = v___x_2046_;
v___y_2013_ = v___y_2035_;
v___y_2014_ = v_ictx_2040_;
v___y_2015_ = v___y_2036_;
v___y_2016_ = v___x_2051_;
goto v___jp_2004_;
}
else
{
lean_dec_ref(v___x_2046_);
lean_dec_ref(v___x_2043_);
lean_dec_ref_known(v_pmctx_2041_, 4);
lean_dec(v___y_2035_);
v___y_1950_ = v___y_2028_;
v___y_1951_ = v___y_2030_;
v___y_1952_ = v___y_2031_;
v___y_1953_ = v___y_2027_;
v___y_1954_ = v___y_2036_;
v___y_1955_ = v_ictx_2040_;
v___y_1956_ = v_s_2047_;
goto v___jp_1949_;
}
}
}
v___jp_2054_:
{
lean_object* v_fileName_2055_; lean_object* v_fileMap_2056_; lean_object* v_options_2057_; lean_object* v_currNamespace_2058_; lean_object* v_openDecls_2059_; uint8_t v_suppressElabErrors_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; 
v_fileName_2055_ = lean_ctor_get(v___y_1909_, 0);
v_fileMap_2056_ = lean_ctor_get(v___y_1909_, 1);
v_options_2057_ = lean_ctor_get(v___y_1909_, 2);
v_currNamespace_2058_ = lean_ctor_get(v___y_1909_, 6);
v_openDecls_2059_ = lean_ctor_get(v___y_1909_, 7);
v_suppressElabErrors_2060_ = lean_ctor_get_uint8(v___y_1909_, sizeof(void*)*14 + 1);
v___x_2061_ = lean_unsigned_to_nat(1u);
v___x_2062_ = l_Lean_Syntax_getArg(v_docComment_1904_, v___x_2061_);
v___x_2063_ = 1;
v___x_2064_ = l_Lean_Syntax_getPos_x3f(v___x_2062_, v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2066_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = l_Lean_Syntax_getTailPos_x3f(v___x_2062_, v___x_2063_);
lean_dec(v___x_2062_);
if (lean_obj_tag(v___x_2066_) == 1)
{
lean_object* v_val_2067_; lean_object* v_source_2068_; lean_object* v___x_2069_; lean_object* v_endPos_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
lean_dec(v_docComment_1904_);
v_val_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_val_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v_source_2068_ = lean_ctor_get(v_fileMap_2056_, 0);
v___x_2069_ = lean_string_utf8_prev(v_source_2068_, v_val_2067_);
lean_dec(v_val_2067_);
v_endPos_2070_ = lean_string_utf8_prev(v_source_2068_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2071_ = lean_string_utf8_byte_size(v_source_2068_);
v___x_2072_ = lean_nat_dec_le(v_endPos_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_endPos_2070_);
v___y_2027_ = v_source_2068_;
v___y_2028_ = v_suppressElabErrors_2060_;
v___y_2029_ = v_options_2057_;
v___y_2030_ = v_fileMap_2056_;
v___y_2031_ = v_fileName_2055_;
v___y_2032_ = v_val_2065_;
v___y_2033_ = v_currNamespace_2058_;
v___y_2034_ = v_openDecls_2059_;
v___y_2035_ = v___x_2061_;
v___y_2036_ = v_suppressElabErrors_2060_;
v___y_2037_ = v___x_2071_;
goto v___jp_2026_;
}
else
{
v___y_2027_ = v_source_2068_;
v___y_2028_ = v_suppressElabErrors_2060_;
v___y_2029_ = v_options_2057_;
v___y_2030_ = v_fileMap_2056_;
v___y_2031_ = v_fileName_2055_;
v___y_2032_ = v_val_2065_;
v___y_2033_ = v_currNamespace_2058_;
v___y_2034_ = v_openDecls_2059_;
v___y_2035_ = v___x_2061_;
v___y_2036_ = v_suppressElabErrors_2060_;
v___y_2037_ = v_endPos_2070_;
goto v___jp_2026_;
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec(v___x_2066_);
lean_dec(v_val_2065_);
v___x_2073_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2074_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1904_, v___x_2073_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v_docComment_1904_);
return v___x_2074_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v___x_2064_);
lean_dec(v___x_2062_);
v___x_2075_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2076_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1904_, v___x_2075_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v_docComment_1904_);
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2141_, lean_object* v_binders_2142_, lean_object* v_docComment_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_){
_start:
{
lean_object* v___x_2151_; lean_object* v_body_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2151_ = lean_unsigned_to_nat(1u);
v_body_2152_ = l_Lean_Syntax_getArg(v_docComment_2143_, v___x_2151_);
v___x_2153_ = 1;
v___x_2154_ = l_Lean_Syntax_getPos_x3f(v_body_2152_, v___x_2153_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2152_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v_body_2152_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec(v_body_2152_);
v___x_2157_ = l_Lean_TSyntax_getDocString(v_docComment_2143_);
lean_dec(v_docComment_2143_);
v___x_2158_ = l_Lean_versoDocStringOfText(v_declName_2141_, v_binders_2142_, v___x_2157_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; 
lean_dec(v_docComment_2143_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = l_Lean_Syntax_getArg(v_body_2152_, v___x_2159_);
lean_dec(v_body_2152_);
v___x_2161_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2160_);
v___x_2162_ = l_Lean_Syntax_isOfKind(v___x_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = l_Lean_Syntax_getArgs(v___x_2160_);
lean_dec(v___x_2160_);
v___x_2164_ = lean_box(0);
v___x_2165_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2141_, v_binders_2142_, v___x_2163_, v___x_2164_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2165_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = l_Lean_Syntax_getArg(v___x_2160_, v___x_2159_);
lean_dec(v___x_2160_);
v___x_2167_ = l_Lean_Syntax_getAtomVal(v___x_2166_);
lean_dec(v___x_2166_);
v___x_2168_ = l_Lean_versoDocStringOfText(v_declName_2141_, v_binders_2142_, v___x_2167_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
return v___x_2168_;
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2154_, 1);
lean_dec(v_body_2152_);
v___x_2169_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2220_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2220_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2220_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
if (lean_obj_tag(v_a_2170_) == 1)
{
lean_object* v_val_2174_; lean_object* v___x_2175_; size_t v_sz_2176_; size_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; 
lean_del_object(v___x_2172_);
v_val_2174_ = lean_ctor_get(v_a_2170_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_a_2170_, 1);
v___x_2175_ = l_Lean_Syntax_getArgs(v_val_2174_);
lean_dec(v_val_2174_);
v_sz_2176_ = lean_array_size(v___x_2175_);
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2176_, v___x_2177_, v___x_2175_);
v___x_2179_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2179_, 0, v___x_2178_);
v___x_2180_ = 0;
v___x_2181_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2141_, v_binders_2142_, v___x_2179_, v___x_2180_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2207_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2207_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2207_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v_fst_2186_; lean_object* v_snd_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2206_; 
v_fst_2186_ = lean_ctor_get(v_a_2182_, 0);
v_snd_2187_ = lean_ctor_get(v_a_2182_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_a_2182_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2189_ = v_a_2182_;
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snd_2187_);
lean_inc(v_fst_2186_);
lean_dec(v_a_2182_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2206_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2205_; 
v_fst_2191_ = lean_ctor_get(v_fst_2186_, 0);
v_snd_2192_ = lean_ctor_get(v_fst_2186_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_fst_2186_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2194_ = v_fst_2186_;
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_snd_2192_);
lean_inc(v_fst_2191_);
lean_dec(v_fst_2186_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2205_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_fst_2191_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_snd_2192_);
v___x_2197_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2199_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2197_);
v___x_2199_ = v___x_2189_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_snd_2187_);
v___x_2199_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2201_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2199_);
v___x_2201_ = v___x_2184_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2199_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
v_a_2208_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2181_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2181_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec(v_a_2170_);
lean_dec(v_binders_2142_);
lean_dec(v_declName_2141_);
v___x_2216_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2216_);
v___x_2218_ = v___x_2172_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_binders_2142_);
lean_dec(v_declName_2141_);
v_a_2221_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2169_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2169_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2229_, lean_object* v_binders_2230_, lean_object* v_docComment_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_versoDocString(v_declName_2229_, v_binders_2230_, v_docComment_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2240_, lean_object* v___x_2241_, lean_object* v_as_2242_, size_t v_sz_2243_, size_t v_i_2244_, lean_object* v_b_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2240_, v___x_2241_, v_as_2242_, v_sz_2243_, v_i_2244_, v_b_2245_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v_as_2256_, lean_object* v_sz_2257_, lean_object* v_i_2258_, lean_object* v_b_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
size_t v_sz_boxed_2267_; size_t v_i_boxed_2268_; lean_object* v_res_2269_; 
v_sz_boxed_2267_ = lean_unbox_usize(v_sz_2257_);
lean_dec(v_sz_2257_);
v_i_boxed_2268_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_res_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2254_, v___x_2255_, v_as_2256_, v_sz_boxed_2267_, v_i_boxed_2268_, v_b_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_as_2256_);
lean_dec(v___x_2255_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2270_, lean_object* v_ref_2271_, lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2271_, v_msg_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2281_, lean_object* v_ref_2282_, lean_object* v_msg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2281_, v_ref_2282_, v_msg_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v_ref_2282_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2292_, lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2302_, v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2312_, lean_object* v_macroStack_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2312_, v_macroStack_2313_, v___y_2318_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2322_, lean_object* v_macroStack_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2322_, v_macroStack_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2332_, lean_object* v_doc_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2341_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2349_; lean_object* v_env_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2341_ = lean_st_ref_get(v_a_2339_);
v_env_2356_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_ref(v_env_2356_);
lean_dec(v___x_2341_);
v___x_2357_ = l_Lean_getMainVersoModuleDocs(v_env_2356_);
v___x_2358_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2357_);
lean_dec_ref(v___x_2357_);
if (lean_obj_tag(v___x_2358_) == 0)
{
v___y_2349_ = v___x_2358_;
goto v___jp_2348_;
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2368_; 
v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_val_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2368_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v_val_2359_, v___x_2363_);
lean_dec(v_val_2359_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2364_);
v___x_2366_ = v___x_2361_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
v___y_2349_ = v___x_2366_;
goto v___jp_2348_;
}
}
}
v___jp_2342_:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2345_, 0, v_range_2332_);
lean_closure_set(v___x_2345_, 1, v___y_2343_);
lean_closure_set(v___x_2345_, 2, v___y_2344_);
v___x_2346_ = 0;
v___x_2347_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2345_, v___x_2346_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
return v___x_2347_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; size_t v_sz_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = l_Lean_Syntax_getArgs(v_doc_2333_);
v_sz_2351_ = lean_array_size(v___x_2350_);
v___x_2352_ = ((size_t)0ULL);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2351_, v___x_2352_, v___x_2350_);
if (lean_obj_tag(v___y_2349_) == 0)
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_unsigned_to_nat(0u);
v___y_2343_ = v___x_2353_;
v___y_2344_ = v___x_2354_;
goto v___jp_2342_;
}
else
{
lean_object* v_val_2355_; 
v_val_2355_ = lean_ctor_get(v___y_2349_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v___y_2349_, 1);
v___y_2343_ = v___x_2353_;
v___y_2344_ = v_val_2355_;
goto v___jp_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2369_, lean_object* v_doc_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_versoModDocString(v_range_2369_, v_doc_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_doc_2370_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2388_, lean_object* v_docComment_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2398_ = l_Lean_versoDocStringOfText(v_declName_2388_, v___x_2397_, v_docComment_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2399_, lean_object* v_docComment_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_versoDocStringFromString(v_declName_2399_, v_docComment_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2409_, lean_object* v_declName_2410_, lean_object* v_env_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_docStringExt;
v___x_2413_ = l_String_removeLeadingSpaces(v_docString_2409_);
v___x_2414_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2412_, v_env_2411_, v_declName_2410_, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2415_, lean_object* v_modifyEnv_2416_, lean_object* v_docString_2417_){
_start:
{
lean_object* v___f_2418_; lean_object* v___x_2419_; 
v___f_2418_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2418_, 0, v_docString_2417_);
lean_closure_set(v___f_2418_, 1, v_declName_2415_);
v___x_2419_ = lean_apply_1(v_modifyEnv_2416_, v___f_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_docComment_2422_, lean_object* v_toBind_2423_, lean_object* v___f_2424_, lean_object* v_____r_2425_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = l_Lean_getDocStringText___redArg(v_inst_2420_, v_inst_2421_, v_docComment_2422_);
v___x_2427_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2426_, v___f_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_docComment_2433_, lean_object* v_toBind_2434_, lean_object* v___f_2435_, lean_object* v_____r_2436_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = l_Lean_validateDocComment___redArg(v_inst_2428_, v_inst_2429_, v_inst_2430_, v_inst_2431_, v_inst_2432_, v_docComment_2433_);
v___x_2438_ = lean_apply_4(v_toBind_2434_, lean_box(0), lean_box(0), v___x_2437_, v___f_2435_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_docComment_2444_, lean_object* v_toBind_2445_, lean_object* v___f_2446_, lean_object* v_____r_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2439_, v_inst_2440_, v_inst_2441_, v_inst_2442_, v_inst_2443_, v_docComment_2444_, v_toBind_2445_, v___f_2446_, v_____r_2447_);
lean_dec(v_docComment_2444_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2449_, lean_object* v_____r_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_apply_1(v___f_2449_, v_____r_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2458_, lean_object* v_declName_2459_, uint8_t v___x_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_toBind_2463_, lean_object* v___f_2464_, lean_object* v_____do__lift_2465_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2465_, v_declName_2459_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_dec(v___f_2464_);
lean_dec(v_toBind_2463_);
lean_dec_ref(v_inst_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec(v_declName_2459_);
goto v___jp_2466_;
}
else
{
lean_dec_ref_known(v___x_2469_, 1);
if (v___x_2460_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_dec(v___f_2458_);
v___x_2470_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2471_ = l_Lean_MessageData_ofConstName(v_declName_2459_, v___x_2460_);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2472_);
lean_ctor_set(v___x_2474_, 1, v___x_2473_);
v___x_2475_ = l_Lean_throwError___redArg(v_inst_2461_, v_inst_2462_, v___x_2474_);
v___x_2476_ = lean_apply_4(v_toBind_2463_, lean_box(0), lean_box(0), v___x_2475_, v___f_2464_);
return v___x_2476_;
}
else
{
lean_dec(v___f_2464_);
lean_dec(v_toBind_2463_);
lean_dec_ref(v_inst_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec(v_declName_2459_);
goto v___jp_2466_;
}
}
v___jp_2466_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_apply_1(v___f_2458_, v___x_2467_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2477_, lean_object* v_declName_2478_, lean_object* v___x_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_toBind_2482_, lean_object* v___f_2483_, lean_object* v_____do__lift_2484_){
_start:
{
uint8_t v___x_390__boxed_2485_; lean_object* v_res_2486_; 
v___x_390__boxed_2485_ = lean_unbox(v___x_2479_);
v_res_2486_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2477_, v_declName_2478_, v___x_390__boxed_2485_, v_inst_2480_, v_inst_2481_, v_toBind_2482_, v___f_2483_, v_____do__lift_2484_);
lean_dec_ref(v_____do__lift_2484_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_declName_2494_, lean_object* v_docComment_2495_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = l_Lean_Name_isAnonymous(v_declName_2494_);
if (v___x_2496_ == 0)
{
lean_object* v_toBind_2497_; lean_object* v_getEnv_2498_; lean_object* v_modifyEnv_2499_; lean_object* v___f_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; 
v_toBind_2497_ = lean_ctor_get(v_inst_2487_, 1);
lean_inc_n(v_toBind_2497_, 4);
v_getEnv_2498_ = lean_ctor_get(v_inst_2490_, 0);
lean_inc(v_getEnv_2498_);
v_modifyEnv_2499_ = lean_ctor_get(v_inst_2490_, 1);
lean_inc(v_modifyEnv_2499_);
lean_dec_ref(v_inst_2490_);
lean_inc(v_declName_2494_);
v___f_2500_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2500_, 0, v_declName_2494_);
lean_closure_set(v___f_2500_, 1, v_modifyEnv_2499_);
lean_inc(v_docComment_2495_);
lean_inc_ref(v_inst_2491_);
lean_inc_ref_n(v_inst_2487_, 2);
v___f_2501_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2501_, 0, v_inst_2487_);
lean_closure_set(v___f_2501_, 1, v_inst_2491_);
lean_closure_set(v___f_2501_, 2, v_docComment_2495_);
lean_closure_set(v___f_2501_, 3, v_toBind_2497_);
lean_closure_set(v___f_2501_, 4, v___f_2500_);
v___f_2502_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2502_, 0, v_inst_2487_);
lean_closure_set(v___f_2502_, 1, v_inst_2488_);
lean_closure_set(v___f_2502_, 2, v_inst_2492_);
lean_closure_set(v___f_2502_, 3, v_inst_2493_);
lean_closure_set(v___f_2502_, 4, v_inst_2489_);
lean_closure_set(v___f_2502_, 5, v_docComment_2495_);
lean_closure_set(v___f_2502_, 6, v_toBind_2497_);
lean_closure_set(v___f_2502_, 7, v___f_2501_);
lean_inc_ref(v___f_2502_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2503_, 0, v___f_2502_);
v___x_2504_ = lean_box(v___x_2496_);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2505_, 0, v___f_2502_);
lean_closure_set(v___f_2505_, 1, v_declName_2494_);
lean_closure_set(v___f_2505_, 2, v___x_2504_);
lean_closure_set(v___f_2505_, 3, v_inst_2487_);
lean_closure_set(v___f_2505_, 4, v_inst_2491_);
lean_closure_set(v___f_2505_, 5, v_toBind_2497_);
lean_closure_set(v___f_2505_, 6, v___f_2503_);
v___x_2506_ = lean_apply_4(v_toBind_2497_, lean_box(0), lean_box(0), v_getEnv_2498_, v___f_2505_);
return v___x_2506_;
}
else
{
lean_object* v_toApplicative_2507_; lean_object* v_toPure_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v_docComment_2495_);
lean_dec(v_declName_2494_);
lean_dec(v_inst_2493_);
lean_dec_ref(v_inst_2492_);
lean_dec_ref(v_inst_2491_);
lean_dec_ref(v_inst_2490_);
lean_dec(v_inst_2489_);
lean_dec(v_inst_2488_);
v_toApplicative_2507_ = lean_ctor_get(v_inst_2487_, 0);
lean_inc_ref(v_toApplicative_2507_);
lean_dec_ref(v_inst_2487_);
v_toPure_2508_ = lean_ctor_get(v_toApplicative_2507_, 1);
lean_inc(v_toPure_2508_);
lean_dec_ref(v_toApplicative_2507_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2509_);
return v___x_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_declName_2519_, lean_object* v_docComment_2520_){
_start:
{
lean_object* v___x_2521_; 
v___x_2521_ = l_Lean_addMarkdownDocString___redArg(v_inst_2512_, v_inst_2513_, v_inst_2514_, v_inst_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_declName_2519_, v_docComment_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2522_, lean_object* v_x1_2523_, lean_object* v_x2_2524_){
_start:
{
lean_object* v_index_2525_; lean_object* v_sourceString_2526_; lean_object* v_imports_2527_; lean_object* v_currNamespace_2528_; lean_object* v_openDecls_2529_; lean_object* v_options_2530_; lean_object* v_check_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2544_; 
v_index_2525_ = lean_ctor_get(v_x2_2524_, 1);
v_sourceString_2526_ = lean_ctor_get(v_x2_2524_, 2);
v_imports_2527_ = lean_ctor_get(v_x2_2524_, 3);
v_currNamespace_2528_ = lean_ctor_get(v_x2_2524_, 4);
v_openDecls_2529_ = lean_ctor_get(v_x2_2524_, 5);
v_options_2530_ = lean_ctor_get(v_x2_2524_, 6);
v_check_2531_ = lean_ctor_get(v_x2_2524_, 7);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_x2_2524_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v_x2_2524_, 0);
lean_dec(v_unused_2545_);
v___x_2533_ = v_x2_2524_;
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_check_2531_);
lean_inc(v_options_2530_);
lean_inc(v_openDecls_2529_);
lean_inc(v_currNamespace_2528_);
lean_inc(v_imports_2527_);
lean_inc(v_sourceString_2526_);
lean_inc(v_index_2525_);
lean_dec(v_x2_2524_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v_toEnvExtension_2536_; lean_object* v_asyncMode_2537_; lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2535_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2536_ = lean_ctor_get(v___x_2535_, 0);
v_asyncMode_2537_ = lean_ctor_get(v_toEnvExtension_2536_, 2);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_declName_2522_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2538_);
v___x_2540_ = v___x_2533_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_index_2525_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_sourceString_2526_);
lean_ctor_set(v_reuseFailAlloc_2543_, 3, v_imports_2527_);
lean_ctor_set(v_reuseFailAlloc_2543_, 4, v_currNamespace_2528_);
lean_ctor_set(v_reuseFailAlloc_2543_, 5, v_openDecls_2529_);
lean_ctor_set(v_reuseFailAlloc_2543_, 6, v_options_2530_);
lean_ctor_set(v_reuseFailAlloc_2543_, 7, v_check_2531_);
v___x_2540_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2535_, v_x1_2523_, v___x_2540_, v_asyncMode_2537_, v___x_2541_);
return v___x_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2565_, lean_object* v_docs_2566_, lean_object* v_deferred_2567_, lean_object* v___f_2568_, lean_object* v_env_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v_env_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2570_ = l_Lean_versoDocStringExt;
v_env_2571_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2570_, v_env_2569_, v_declName_2565_, v_docs_2566_);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = lean_array_get_size(v_deferred_2567_);
v___x_2574_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2575_ = lean_nat_dec_lt(v___x_2572_, v___x_2573_);
if (v___x_2575_ == 0)
{
lean_dec_ref(v___f_2568_);
lean_dec_ref(v_deferred_2567_);
return v_env_2571_;
}
else
{
uint8_t v___x_2576_; 
v___x_2576_ = lean_nat_dec_le(v___x_2573_, v___x_2573_);
if (v___x_2576_ == 0)
{
if (v___x_2575_ == 0)
{
lean_dec_ref(v___f_2568_);
lean_dec_ref(v_deferred_2567_);
return v_env_2571_;
}
else
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = lean_usize_of_nat(v___x_2573_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2574_, v___f_2568_, v_deferred_2567_, v___x_2577_, v___x_2578_, v_env_2571_);
return v___x_2579_;
}
}
else
{
size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = lean_usize_of_nat(v___x_2573_);
v___x_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2574_, v___f_2568_, v_deferred_2567_, v___x_2580_, v___x_2581_, v_env_2571_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2583_, lean_object* v___f_2584_, lean_object* v_____r_2585_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_apply_1(v_modifyEnv_2583_, v___f_2584_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2589_, lean_object* v_modifyEnv_2590_, lean_object* v___f_2591_, uint8_t v___x_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_toBind_2595_, lean_object* v___f_2596_, lean_object* v_____do__lift_2597_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2597_, v_declName_2589_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; 
lean_dec(v___f_2596_);
lean_dec(v_toBind_2595_);
lean_dec_ref(v_inst_2594_);
lean_dec_ref(v_inst_2593_);
lean_dec(v_declName_2589_);
v___x_2599_ = lean_apply_1(v_modifyEnv_2590_, v___f_2591_);
return v___x_2599_;
}
else
{
lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2616_; 
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v___x_2598_, 0);
lean_dec(v_unused_2617_);
v___x_2601_ = v___x_2598_;
v_isShared_2602_ = v_isSharedCheck_2616_;
goto v_resetjp_2600_;
}
else
{
lean_dec(v___x_2598_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2616_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
if (v___x_2592_ == 0)
{
lean_object* v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec_ref(v___f_2591_);
lean_dec(v_modifyEnv_2590_);
v___x_2603_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2604_ = 1;
v___x_2605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2589_, v___x_2604_);
v___x_2606_ = lean_string_append(v___x_2603_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2608_ = lean_string_append(v___x_2606_, v___x_2607_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 3);
lean_ctor_set(v___x_2601_, 0, v___x_2608_);
v___x_2610_ = v___x_2601_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = l_Lean_MessageData_ofFormat(v___x_2610_);
v___x_2612_ = l_Lean_throwError___redArg(v_inst_2593_, v_inst_2594_, v___x_2611_);
v___x_2613_ = lean_apply_4(v_toBind_2595_, lean_box(0), lean_box(0), v___x_2612_, v___f_2596_);
return v___x_2613_;
}
}
else
{
lean_object* v___x_2615_; 
lean_del_object(v___x_2601_);
lean_dec(v___f_2596_);
lean_dec(v_toBind_2595_);
lean_dec_ref(v_inst_2594_);
lean_dec_ref(v_inst_2593_);
lean_dec(v_declName_2589_);
v___x_2615_ = lean_apply_1(v_modifyEnv_2590_, v___f_2591_);
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2618_, lean_object* v_modifyEnv_2619_, lean_object* v___f_2620_, lean_object* v___x_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_toBind_2624_, lean_object* v___f_2625_, lean_object* v_____do__lift_2626_){
_start:
{
uint8_t v___x_577__boxed_2627_; lean_object* v_res_2628_; 
v___x_577__boxed_2627_ = lean_unbox(v___x_2621_);
v_res_2628_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2618_, v_modifyEnv_2619_, v___f_2620_, v___x_577__boxed_2627_, v_inst_2622_, v_inst_2623_, v_toBind_2624_, v___f_2625_, v_____do__lift_2626_);
lean_dec_ref(v_____do__lift_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_declName_2632_, lean_object* v_docs_2633_, lean_object* v_deferred_2634_){
_start:
{
uint8_t v___x_2635_; 
v___x_2635_ = l_Lean_Name_isAnonymous(v_declName_2632_);
if (v___x_2635_ == 0)
{
lean_object* v_toBind_2636_; lean_object* v_getEnv_2637_; lean_object* v_modifyEnv_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; 
v_toBind_2636_ = lean_ctor_get(v_inst_2629_, 1);
lean_inc_n(v_toBind_2636_, 2);
v_getEnv_2637_ = lean_ctor_get(v_inst_2630_, 0);
lean_inc(v_getEnv_2637_);
v_modifyEnv_2638_ = lean_ctor_get(v_inst_2630_, 1);
lean_inc_n(v_modifyEnv_2638_, 2);
lean_dec_ref(v_inst_2630_);
lean_inc_n(v_declName_2632_, 2);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2639_, 0, v_declName_2632_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2640_, 0, v_declName_2632_);
lean_closure_set(v___f_2640_, 1, v_docs_2633_);
lean_closure_set(v___f_2640_, 2, v_deferred_2634_);
lean_closure_set(v___f_2640_, 3, v___f_2639_);
lean_inc_ref(v___f_2640_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2641_, 0, v_modifyEnv_2638_);
lean_closure_set(v___f_2641_, 1, v___f_2640_);
v___x_2642_ = lean_box(v___x_2635_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2643_, 0, v_declName_2632_);
lean_closure_set(v___f_2643_, 1, v_modifyEnv_2638_);
lean_closure_set(v___f_2643_, 2, v___f_2640_);
lean_closure_set(v___f_2643_, 3, v___x_2642_);
lean_closure_set(v___f_2643_, 4, v_inst_2629_);
lean_closure_set(v___f_2643_, 5, v_inst_2631_);
lean_closure_set(v___f_2643_, 6, v_toBind_2636_);
lean_closure_set(v___f_2643_, 7, v___f_2641_);
v___x_2644_ = lean_apply_4(v_toBind_2636_, lean_box(0), lean_box(0), v_getEnv_2637_, v___f_2643_);
return v___x_2644_;
}
else
{
lean_object* v_toApplicative_2645_; lean_object* v_toPure_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v_deferred_2634_);
lean_dec_ref(v_docs_2633_);
lean_dec(v_declName_2632_);
lean_dec_ref(v_inst_2631_);
lean_dec_ref(v_inst_2630_);
v_toApplicative_2645_ = lean_ctor_get(v_inst_2629_, 0);
lean_inc_ref(v_toApplicative_2645_);
lean_dec_ref(v_inst_2629_);
v_toPure_2646_ = lean_ctor_get(v_toApplicative_2645_, 1);
lean_inc(v_toPure_2646_);
lean_dec_ref(v_toApplicative_2645_);
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_apply_2(v_toPure_2646_, lean_box(0), v___x_2647_);
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_declName_2654_, lean_object* v_docs_2655_, lean_object* v_deferred_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2650_, v_inst_2651_, v_inst_2653_, v_declName_2654_, v_docs_2655_, v_deferred_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2658_, lean_object* v_inst_2659_, lean_object* v_inst_2660_, lean_object* v_inst_2661_, lean_object* v_inst_2662_, lean_object* v_declName_2663_, lean_object* v_docs_2664_, lean_object* v_deferred_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_addVersoDocStringCore(v_m_2658_, v_inst_2659_, v_inst_2660_, v_inst_2661_, v_inst_2662_, v_declName_2663_, v_docs_2664_, v_deferred_2665_);
lean_dec(v_inst_2661_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2667_, lean_object* v_x1_2668_, lean_object* v_x2_2669_){
_start:
{
lean_object* v_index_2670_; lean_object* v_sourceString_2671_; lean_object* v_imports_2672_; lean_object* v_currNamespace_2673_; lean_object* v_openDecls_2674_; lean_object* v_options_2675_; lean_object* v_check_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2689_; 
v_index_2670_ = lean_ctor_get(v_x2_2669_, 1);
v_sourceString_2671_ = lean_ctor_get(v_x2_2669_, 2);
v_imports_2672_ = lean_ctor_get(v_x2_2669_, 3);
v_currNamespace_2673_ = lean_ctor_get(v_x2_2669_, 4);
v_openDecls_2674_ = lean_ctor_get(v_x2_2669_, 5);
v_options_2675_ = lean_ctor_get(v_x2_2669_, 6);
v_check_2676_ = lean_ctor_get(v_x2_2669_, 7);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_x2_2669_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v_x2_2669_, 0);
lean_dec(v_unused_2690_);
v___x_2678_ = v_x2_2669_;
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_check_2676_);
lean_inc(v_options_2675_);
lean_inc(v_openDecls_2674_);
lean_inc(v_currNamespace_2673_);
lean_inc(v_imports_2672_);
lean_inc(v_sourceString_2671_);
lean_inc(v_index_2670_);
lean_dec(v_x2_2669_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v_toEnvExtension_2681_; lean_object* v_asyncMode_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2680_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2681_ = lean_ctor_get(v___x_2680_, 0);
v_asyncMode_2682_ = lean_ctor_get(v_toEnvExtension_2681_, 2);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_size_2667_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2683_);
v___x_2685_ = v___x_2678_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_index_2670_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_sourceString_2671_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_imports_2672_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_currNamespace_2673_);
lean_ctor_set(v_reuseFailAlloc_2688_, 5, v_openDecls_2674_);
lean_ctor_set(v_reuseFailAlloc_2688_, 6, v_options_2675_);
lean_ctor_set(v_reuseFailAlloc_2688_, 7, v_check_2676_);
v___x_2685_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2680_, v_x1_2668_, v___x_2685_, v_asyncMode_2682_, v___x_2686_);
return v___x_2687_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2693_ = l_Lean_stringToMessageData(v___x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_deferred_2697_, lean_object* v_inst_2698_, lean_object* v___f_2699_, lean_object* v_____do__lift_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2700_, v_docs_2694_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec_ref(v___f_2699_);
lean_dec_ref(v_inst_2698_);
lean_dec_ref(v_deferred_2697_);
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2704_ = l_Lean_stringToMessageData(v_a_2702_);
v___x_2705_ = l_Lean_indentD(v___x_2704_);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2703_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_throwError___redArg(v_inst_2695_, v_inst_2696_, v___x_2706_);
return v___x_2707_;
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
lean_dec_ref(v_inst_2696_);
lean_dec_ref(v_inst_2695_);
v_a_2708_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2709_ = lean_unsigned_to_nat(0u);
v___x_2710_ = lean_array_get_size(v_deferred_2697_);
v___x_2711_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2712_ = lean_nat_dec_lt(v___x_2709_, v___x_2710_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; 
lean_dec_ref(v___f_2699_);
lean_dec_ref(v_deferred_2697_);
v___x_2713_ = l_Lean_setEnv___redArg(v_inst_2698_, v_a_2708_);
return v___x_2713_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_nat_dec_le(v___x_2710_, v___x_2710_);
if (v___x_2714_ == 0)
{
if (v___x_2712_ == 0)
{
lean_object* v___x_2715_; 
lean_dec_ref(v___f_2699_);
lean_dec_ref(v_deferred_2697_);
v___x_2715_ = l_Lean_setEnv___redArg(v_inst_2698_, v_a_2708_);
return v___x_2715_;
}
else
{
size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = lean_usize_of_nat(v___x_2710_);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2711_, v___f_2699_, v_deferred_2697_, v___x_2716_, v___x_2717_, v_a_2708_);
v___x_2719_ = l_Lean_setEnv___redArg(v_inst_2698_, v___x_2718_);
return v___x_2719_;
}
}
else
{
size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2720_ = ((size_t)0ULL);
v___x_2721_ = lean_usize_of_nat(v___x_2710_);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2711_, v___f_2699_, v_deferred_2697_, v___x_2720_, v___x_2721_, v_a_2708_);
v___x_2723_ = l_Lean_setEnv___redArg(v_inst_2698_, v___x_2722_);
return v___x_2723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_deferred_2727_, lean_object* v_inst_2728_, lean_object* v_toBind_2729_, lean_object* v_getEnv_2730_, lean_object* v_____do__lift_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v_size_2733_; lean_object* v___f_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; 
v___x_2732_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2731_);
v_size_2733_ = lean_ctor_get(v___x_2732_, 2);
lean_inc(v_size_2733_);
lean_dec_ref(v___x_2732_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2734_, 0, v_size_2733_);
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2735_, 0, v_docs_2724_);
lean_closure_set(v___f_2735_, 1, v_inst_2725_);
lean_closure_set(v___f_2735_, 2, v_inst_2726_);
lean_closure_set(v___f_2735_, 3, v_deferred_2727_);
lean_closure_set(v___f_2735_, 4, v_inst_2728_);
lean_closure_set(v___f_2735_, 5, v___f_2734_);
v___x_2736_ = lean_apply_4(v_toBind_2729_, lean_box(0), lean_box(0), v_getEnv_2730_, v___f_2735_);
return v___x_2736_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2739_ = l_Lean_stringToMessageData(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_toBind_2742_, lean_object* v_getEnv_2743_, lean_object* v___f_2744_, lean_object* v_____do__lift_2745_){
_start:
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = l_Lean_getMainModuleDoc(v_____do__lift_2745_);
v___x_2747_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2746_);
lean_dec_ref(v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
lean_dec(v___f_2744_);
lean_dec(v_getEnv_2743_);
lean_dec(v_toBind_2742_);
v___x_2748_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2749_ = l_Lean_throwError___redArg(v_inst_2740_, v_inst_2741_, v___x_2748_);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_inst_2741_);
lean_dec_ref(v_inst_2740_);
v___x_2750_ = lean_apply_4(v_toBind_2742_, lean_box(0), lean_box(0), v_getEnv_2743_, v___f_2744_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_inst_2753_, lean_object* v_docs_2754_, lean_object* v_deferred_2755_){
_start:
{
lean_object* v_toBind_2756_; lean_object* v_getEnv_2757_; lean_object* v___f_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; 
v_toBind_2756_ = lean_ctor_get(v_inst_2751_, 1);
lean_inc_n(v_toBind_2756_, 3);
v_getEnv_2757_ = lean_ctor_get(v_inst_2752_, 0);
lean_inc_n(v_getEnv_2757_, 3);
lean_inc_ref(v_inst_2753_);
lean_inc_ref(v_inst_2751_);
v___f_2758_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2758_, 0, v_docs_2754_);
lean_closure_set(v___f_2758_, 1, v_inst_2751_);
lean_closure_set(v___f_2758_, 2, v_inst_2753_);
lean_closure_set(v___f_2758_, 3, v_deferred_2755_);
lean_closure_set(v___f_2758_, 4, v_inst_2752_);
lean_closure_set(v___f_2758_, 5, v_toBind_2756_);
lean_closure_set(v___f_2758_, 6, v_getEnv_2757_);
v___f_2759_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2759_, 0, v_inst_2751_);
lean_closure_set(v___f_2759_, 1, v_inst_2753_);
lean_closure_set(v___f_2759_, 2, v_toBind_2756_);
lean_closure_set(v___f_2759_, 3, v_getEnv_2757_);
lean_closure_set(v___f_2759_, 4, v___f_2758_);
v___x_2760_ = lean_apply_4(v_toBind_2756_, lean_box(0), lean_box(0), v_getEnv_2757_, v___f_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2761_, lean_object* v_inst_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_inst_2765_, lean_object* v_docs_2766_, lean_object* v_deferred_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2762_, v_inst_2763_, v_inst_2765_, v_docs_2766_, v_deferred_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_inst_2772_, lean_object* v_inst_2773_, lean_object* v_docs_2774_, lean_object* v_deferred_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_addVersoModDocStringCore(v_m_2769_, v_inst_2770_, v_inst_2771_, v_inst_2772_, v_inst_2773_, v_docs_2774_, v_deferred_2775_);
lean_dec(v_inst_2772_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2777_, lean_object* v_as_2778_, size_t v_i_2779_, size_t v_stop_2780_, lean_object* v_b_2781_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_usize_dec_eq(v_i_2779_, v_stop_2780_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v_index_2784_; lean_object* v_sourceString_2785_; lean_object* v_imports_2786_; lean_object* v_currNamespace_2787_; lean_object* v_openDecls_2788_; lean_object* v_options_2789_; lean_object* v_check_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2806_; 
v___x_2783_ = lean_array_uget(v_as_2778_, v_i_2779_);
v_index_2784_ = lean_ctor_get(v___x_2783_, 1);
v_sourceString_2785_ = lean_ctor_get(v___x_2783_, 2);
v_imports_2786_ = lean_ctor_get(v___x_2783_, 3);
v_currNamespace_2787_ = lean_ctor_get(v___x_2783_, 4);
v_openDecls_2788_ = lean_ctor_get(v___x_2783_, 5);
v_options_2789_ = lean_ctor_get(v___x_2783_, 6);
v_check_2790_ = lean_ctor_get(v___x_2783_, 7);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2783_, 0);
lean_dec(v_unused_2807_);
v___x_2792_ = v___x_2783_;
v_isShared_2793_ = v_isSharedCheck_2806_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_check_2790_);
lean_inc(v_options_2789_);
lean_inc(v_openDecls_2788_);
lean_inc(v_currNamespace_2787_);
lean_inc(v_imports_2786_);
lean_inc(v_sourceString_2785_);
lean_inc(v_index_2784_);
lean_dec(v___x_2783_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2806_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v_toEnvExtension_2795_; lean_object* v_asyncMode_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2794_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2795_ = lean_ctor_get(v___x_2794_, 0);
v_asyncMode_2796_ = lean_ctor_get(v_toEnvExtension_2795_, 2);
lean_inc(v_declName_2777_);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_declName_2777_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2797_);
v___x_2799_ = v___x_2792_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_index_2784_);
lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_sourceString_2785_);
lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_imports_2786_);
lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_currNamespace_2787_);
lean_ctor_set(v_reuseFailAlloc_2805_, 5, v_openDecls_2788_);
lean_ctor_set(v_reuseFailAlloc_2805_, 6, v_options_2789_);
lean_ctor_set(v_reuseFailAlloc_2805_, 7, v_check_2790_);
v___x_2799_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; size_t v___x_2802_; size_t v___x_2803_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2794_, v_b_2781_, v___x_2799_, v_asyncMode_2796_, v___x_2800_);
v___x_2802_ = ((size_t)1ULL);
v___x_2803_ = lean_usize_add(v_i_2779_, v___x_2802_);
v_i_2779_ = v___x_2803_;
v_b_2781_ = v___x_2801_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2777_);
return v_b_2781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_stop_2811_, lean_object* v_b_2812_){
_start:
{
size_t v_i_boxed_2813_; size_t v_stop_boxed_2814_; lean_object* v_res_2815_; 
v_i_boxed_2813_ = lean_unbox_usize(v_i_2810_);
lean_dec(v_i_2810_);
v_stop_boxed_2814_ = lean_unbox_usize(v_stop_2811_);
lean_dec(v_stop_2811_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2808_, v_as_2809_, v_i_boxed_2813_, v_stop_boxed_2814_, v_b_2812_);
lean_dec_ref(v_as_2809_);
return v_res_2815_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2816_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
return v___x_2820_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2822_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
lean_ctor_set(v___x_2822_, 2, v___x_2821_);
lean_ctor_set(v___x_2822_, 3, v___x_2821_);
lean_ctor_set(v___x_2822_, 4, v___x_2821_);
lean_ctor_set(v___x_2822_, 5, v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2823_, lean_object* v_docs_2824_, lean_object* v_deferred_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2865_; lean_object* v___y_2866_; uint8_t v___x_2888_; 
v___x_2888_ = l_Lean_Name_isAnonymous(v_declName_2823_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; lean_object* v_env_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_st_ref_get(v___y_2831_);
v_env_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc_ref(v_env_2890_);
lean_dec(v___x_2889_);
v___x_2891_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2890_, v_declName_2823_);
lean_dec_ref(v_env_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
v___y_2865_ = v___y_2829_;
v___y_2866_ = v___y_2831_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2906_; 
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2906_ == 0)
{
lean_object* v_unused_2907_; 
v_unused_2907_ = lean_ctor_get(v___x_2891_, 0);
lean_dec(v_unused_2907_);
v___x_2893_ = v___x_2891_;
v_isShared_2894_ = v_isSharedCheck_2906_;
goto v_resetjp_2892_;
}
else
{
lean_dec(v___x_2891_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2906_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
if (v___x_2888_ == 0)
{
lean_object* v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
lean_dec_ref(v_docs_2824_);
v___x_2895_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2896_ = 1;
v___x_2897_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2823_, v___x_2896_);
v___x_2898_ = lean_string_append(v___x_2895_, v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set_tag(v___x_2893_, 3);
lean_ctor_set(v___x_2893_, 0, v___x_2900_);
v___x_2902_ = v___x_2893_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = l_Lean_MessageData_ofFormat(v___x_2902_);
v___x_2904_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2903_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2904_;
}
}
else
{
lean_del_object(v___x_2893_);
v___y_2865_ = v___y_2829_;
v___y_2866_ = v___y_2831_;
goto v___jp_2864_;
}
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec_ref(v_docs_2824_);
lean_dec(v_declName_2823_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
v___jp_2833_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_mctx_2848_; lean_object* v_zetaDeltaFVarIds_2849_; lean_object* v_postponed_2850_; lean_object* v_diag_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2862_; 
v___x_2844_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2845_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2845_, 0, v___y_2843_);
lean_ctor_set(v___x_2845_, 1, v___y_2836_);
lean_ctor_set(v___x_2845_, 2, v___y_2834_);
lean_ctor_set(v___x_2845_, 3, v___y_2841_);
lean_ctor_set(v___x_2845_, 4, v___y_2840_);
lean_ctor_set(v___x_2845_, 5, v___x_2844_);
lean_ctor_set(v___x_2845_, 6, v___y_2838_);
lean_ctor_set(v___x_2845_, 7, v___y_2842_);
lean_ctor_set(v___x_2845_, 8, v___y_2839_);
v___x_2846_ = lean_st_ref_set(v___y_2837_, v___x_2845_);
v___x_2847_ = lean_st_ref_take(v___y_2835_);
v_mctx_2848_ = lean_ctor_get(v___x_2847_, 0);
v_zetaDeltaFVarIds_2849_ = lean_ctor_get(v___x_2847_, 2);
v_postponed_2850_ = lean_ctor_get(v___x_2847_, 3);
v_diag_2851_ = lean_ctor_get(v___x_2847_, 4);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v___x_2847_, 1);
lean_dec(v_unused_2863_);
v___x_2853_ = v___x_2847_;
v_isShared_2854_ = v_isSharedCheck_2862_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_diag_2851_);
lean_inc(v_postponed_2850_);
lean_inc(v_zetaDeltaFVarIds_2849_);
lean_inc(v_mctx_2848_);
lean_dec(v___x_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2862_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 1, v___x_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_mctx_2848_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_zetaDeltaFVarIds_2849_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_postponed_2850_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_diag_2851_);
v___x_2857_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_st_ref_set(v___y_2835_, v___x_2857_);
v___x_2859_ = lean_box(0);
v___x_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
return v___x_2860_;
}
}
}
v___jp_2864_:
{
lean_object* v___x_2867_; lean_object* v_env_2868_; lean_object* v_nextMacroScope_2869_; lean_object* v_ngen_2870_; lean_object* v_auxDeclNGen_2871_; lean_object* v_traceState_2872_; lean_object* v_messages_2873_; lean_object* v_infoState_2874_; lean_object* v_snapshotTasks_2875_; lean_object* v___x_2876_; lean_object* v_env_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2867_ = lean_st_ref_take(v___y_2866_);
v_env_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc_ref(v_env_2868_);
v_nextMacroScope_2869_ = lean_ctor_get(v___x_2867_, 1);
lean_inc(v_nextMacroScope_2869_);
v_ngen_2870_ = lean_ctor_get(v___x_2867_, 2);
lean_inc_ref(v_ngen_2870_);
v_auxDeclNGen_2871_ = lean_ctor_get(v___x_2867_, 3);
lean_inc_ref(v_auxDeclNGen_2871_);
v_traceState_2872_ = lean_ctor_get(v___x_2867_, 4);
lean_inc_ref(v_traceState_2872_);
v_messages_2873_ = lean_ctor_get(v___x_2867_, 6);
lean_inc_ref(v_messages_2873_);
v_infoState_2874_ = lean_ctor_get(v___x_2867_, 7);
lean_inc_ref(v_infoState_2874_);
v_snapshotTasks_2875_ = lean_ctor_get(v___x_2867_, 8);
lean_inc_ref(v_snapshotTasks_2875_);
lean_dec(v___x_2867_);
v___x_2876_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2823_);
v_env_2877_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2876_, v_env_2868_, v_declName_2823_, v_docs_2824_);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = lean_array_get_size(v_deferred_2825_);
v___x_2880_ = lean_nat_dec_lt(v___x_2878_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_dec(v_declName_2823_);
v___y_2834_ = v_ngen_2870_;
v___y_2835_ = v___y_2865_;
v___y_2836_ = v_nextMacroScope_2869_;
v___y_2837_ = v___y_2866_;
v___y_2838_ = v_messages_2873_;
v___y_2839_ = v_snapshotTasks_2875_;
v___y_2840_ = v_traceState_2872_;
v___y_2841_ = v_auxDeclNGen_2871_;
v___y_2842_ = v_infoState_2874_;
v___y_2843_ = v_env_2877_;
goto v___jp_2833_;
}
else
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_nat_dec_le(v___x_2879_, v___x_2879_);
if (v___x_2881_ == 0)
{
if (v___x_2880_ == 0)
{
lean_dec(v_declName_2823_);
v___y_2834_ = v_ngen_2870_;
v___y_2835_ = v___y_2865_;
v___y_2836_ = v_nextMacroScope_2869_;
v___y_2837_ = v___y_2866_;
v___y_2838_ = v_messages_2873_;
v___y_2839_ = v_snapshotTasks_2875_;
v___y_2840_ = v_traceState_2872_;
v___y_2841_ = v_auxDeclNGen_2871_;
v___y_2842_ = v_infoState_2874_;
v___y_2843_ = v_env_2877_;
goto v___jp_2833_;
}
else
{
size_t v___x_2882_; size_t v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((size_t)0ULL);
v___x_2883_ = lean_usize_of_nat(v___x_2879_);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2823_, v_deferred_2825_, v___x_2882_, v___x_2883_, v_env_2877_);
v___y_2834_ = v_ngen_2870_;
v___y_2835_ = v___y_2865_;
v___y_2836_ = v_nextMacroScope_2869_;
v___y_2837_ = v___y_2866_;
v___y_2838_ = v_messages_2873_;
v___y_2839_ = v_snapshotTasks_2875_;
v___y_2840_ = v_traceState_2872_;
v___y_2841_ = v_auxDeclNGen_2871_;
v___y_2842_ = v_infoState_2874_;
v___y_2843_ = v___x_2884_;
goto v___jp_2833_;
}
}
else
{
size_t v___x_2885_; size_t v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = ((size_t)0ULL);
v___x_2886_ = lean_usize_of_nat(v___x_2879_);
v___x_2887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2823_, v_deferred_2825_, v___x_2885_, v___x_2886_, v_env_2877_);
v___y_2834_ = v_ngen_2870_;
v___y_2835_ = v___y_2865_;
v___y_2836_ = v_nextMacroScope_2869_;
v___y_2837_ = v___y_2866_;
v___y_2838_ = v_messages_2873_;
v___y_2839_ = v_snapshotTasks_2875_;
v___y_2840_ = v_traceState_2872_;
v___y_2841_ = v_auxDeclNGen_2871_;
v___y_2842_ = v_infoState_2874_;
v___y_2843_ = v___x_2887_;
goto v___jp_2833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2910_, lean_object* v_docs_2911_, lean_object* v_deferred_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2910_, v_docs_2911_, v_deferred_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v_deferred_2912_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2921_, lean_object* v_binders_2922_, lean_object* v_docComment_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___x_2951_; lean_object* v_env_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_st_ref_get(v_a_2929_);
v_env_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc_ref(v_env_2952_);
lean_dec(v___x_2951_);
v___x_2953_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2952_, v_declName_2921_);
lean_dec_ref(v_env_2952_);
if (lean_obj_tag(v___x_2953_) == 0)
{
v___y_2932_ = v_a_2924_;
v___y_2933_ = v_a_2925_;
v___y_2934_ = v_a_2926_;
v___y_2935_ = v_a_2927_;
v___y_2936_ = v_a_2928_;
v___y_2937_ = v_a_2929_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_docComment_2923_);
lean_dec(v_binders_2922_);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2953_, 0);
lean_dec(v_unused_2969_);
v___x_2955_ = v___x_2953_;
v_isShared_2956_ = v_isSharedCheck_2968_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v___x_2953_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2968_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; uint8_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2957_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2958_ = 1;
v___x_2959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2921_, v___x_2958_);
v___x_2960_ = lean_string_append(v___x_2957_, v___x_2959_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2962_ = lean_string_append(v___x_2960_, v___x_2961_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 3);
lean_ctor_set(v___x_2955_, 0, v___x_2962_);
v___x_2964_ = v___x_2955_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = l_Lean_MessageData_ofFormat(v___x_2964_);
v___x_2966_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2965_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
return v___x_2966_;
}
}
}
v___jp_2931_:
{
lean_object* v___x_2938_; 
lean_inc(v_declName_2921_);
v___x_2938_ = l_Lean_versoDocString(v_declName_2921_, v_binders_2922_, v_docComment_2923_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v_toVersoDocString_2940_; lean_object* v_deferredChecks_2941_; lean_object* v___x_2942_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v_toVersoDocString_2940_ = lean_ctor_get(v_a_2939_, 0);
lean_inc_ref(v_toVersoDocString_2940_);
v_deferredChecks_2941_ = lean_ctor_get(v_a_2939_, 1);
lean_inc_ref(v_deferredChecks_2941_);
lean_dec(v_a_2939_);
v___x_2942_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2921_, v_toVersoDocString_2940_, v_deferredChecks_2941_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v_deferredChecks_2941_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec(v_declName_2921_);
v_a_2943_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2938_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2938_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2970_, lean_object* v_binders_2971_, lean_object* v_docComment_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_addVersoDocString(v_declName_2970_, v_binders_2971_, v_docComment_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec_ref(v_a_2973_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2981_, lean_object* v_docComment_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v___x_3012_; 
v___x_3010_ = lean_st_ref_get(v_a_2988_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3012_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3011_, v_declName_2981_);
lean_dec_ref(v_env_3011_);
if (lean_obj_tag(v___x_3012_) == 0)
{
v___y_2991_ = v_a_2983_;
v___y_2992_ = v_a_2984_;
v___y_2993_ = v_a_2985_;
v___y_2994_ = v_a_2986_;
v___y_2995_ = v_a_2987_;
v___y_2996_ = v_a_2988_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3027_; 
lean_dec_ref(v_docComment_2982_);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v___x_3012_, 0);
lean_dec(v_unused_3028_);
v___x_3014_ = v___x_3012_;
v_isShared_3015_ = v_isSharedCheck_3027_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v___x_3012_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3027_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v___x_3016_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_3017_ = 1;
v___x_3018_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2981_, v___x_3017_);
v___x_3019_ = lean_string_append(v___x_3016_, v___x_3018_);
lean_dec_ref(v___x_3018_);
v___x_3020_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_3021_ = lean_string_append(v___x_3019_, v___x_3020_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set_tag(v___x_3014_, 3);
lean_ctor_set(v___x_3014_, 0, v___x_3021_);
v___x_3023_ = v___x_3014_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3021_);
v___x_3023_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = l_Lean_MessageData_ofFormat(v___x_3023_);
v___x_3025_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3024_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
return v___x_3025_;
}
}
}
v___jp_2990_:
{
lean_object* v___x_2997_; 
lean_inc(v_declName_2981_);
v___x_2997_ = l_Lean_versoDocStringFromString(v_declName_2981_, v_docComment_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_toVersoDocString_2999_; lean_object* v_deferredChecks_3000_; lean_object* v___x_3001_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v_toVersoDocString_2999_ = lean_ctor_get(v_a_2998_, 0);
lean_inc_ref(v_toVersoDocString_2999_);
v_deferredChecks_3000_ = lean_ctor_get(v_a_2998_, 1);
lean_inc_ref(v_deferredChecks_3000_);
lean_dec(v_a_2998_);
v___x_3001_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2981_, v_toVersoDocString_2999_, v_deferredChecks_3000_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec_ref(v_deferredChecks_3000_);
return v___x_3001_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_declName_2981_);
v_a_3002_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2997_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2997_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_3029_, lean_object* v_docComment_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_addVersoDocStringFromString(v_declName_3029_, v_docComment_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3039_, lean_object* v_msgData_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
uint8_t v___x_3046_; uint8_t v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = 2;
v___x_3047_ = 0;
v___x_3048_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_3039_, v_msgData_3040_, v___x_3046_, v___x_3047_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3049_, lean_object* v_msgData_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3049_, v_msgData_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v_ref_3049_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3057_, lean_object* v_str_3058_, lean_object* v_as_3059_, size_t v_sz_3060_, size_t v_i_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_a_3071_; uint8_t v___x_3075_; 
v___x_3075_ = lean_usize_dec_lt(v_i_3061_, v_sz_3060_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v_b_3062_);
return v___x_3076_;
}
else
{
lean_object* v_a_3077_; lean_object* v_fst_3078_; lean_object* v_snd_3079_; lean_object* v_start_3080_; lean_object* v_stop_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3101_; 
v_a_3077_ = lean_array_uget_borrowed(v_as_3059_, v_i_3061_);
v_fst_3078_ = lean_ctor_get(v_a_3077_, 0);
lean_inc(v_fst_3078_);
v_snd_3079_ = lean_ctor_get(v_a_3077_, 1);
v_start_3080_ = lean_ctor_get(v_fst_3078_, 0);
v_stop_3081_ = lean_ctor_get(v_fst_3078_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_fst_3078_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3083_ = v_fst_3078_;
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_stop_3081_);
lean_inc(v_start_3080_);
lean_dec(v_fst_3078_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_box(0);
if (lean_obj_tag(v___y_3057_) == 1)
{
lean_object* v_val_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v_val_3086_ = lean_ctor_get(v___y_3057_, 0);
v___x_3087_ = lean_nat_add(v_val_3086_, v_start_3080_);
v___x_3088_ = lean_nat_add(v_val_3086_, v_stop_3081_);
v___x_3089_ = 0;
v___x_3090_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3090_, 0, v___x_3087_);
lean_ctor_set(v___x_3090_, 1, v___x_3088_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*2, v___x_3089_);
v___x_3091_ = lean_string_utf8_extract(v_str_3058_, v_start_3080_, v_stop_3081_);
lean_dec(v_stop_3081_);
lean_dec(v_start_3080_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 2);
lean_ctor_set(v___x_3083_, 1, v___x_3091_);
lean_ctor_set(v___x_3083_, 0, v___x_3090_);
v___x_3093_ = v___x_3083_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_inc(v_snd_3079_);
v___x_3094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_snd_3079_);
v___x_3095_ = l_Lean_MessageData_ofFormat(v___x_3094_);
v___x_3096_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3093_, v___x_3095_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec_ref(v___x_3093_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref_known(v___x_3096_, 1);
v_a_3071_ = v___x_3085_;
goto v___jp_3070_;
}
else
{
return v___x_3096_;
}
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_del_object(v___x_3083_);
lean_dec(v_stop_3081_);
lean_dec(v_start_3080_);
lean_inc(v_snd_3079_);
v___x_3098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_snd_3079_);
v___x_3099_ = l_Lean_MessageData_ofFormat(v___x_3098_);
v___x_3100_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3099_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_dec_ref_known(v___x_3100_, 1);
v_a_3071_ = v___x_3085_;
goto v___jp_3070_;
}
else
{
return v___x_3100_;
}
}
}
}
v___jp_3070_:
{
size_t v___x_3072_; size_t v___x_3073_; 
v___x_3072_ = ((size_t)1ULL);
v___x_3073_ = lean_usize_add(v_i_3061_, v___x_3072_);
v_i_3061_ = v___x_3073_;
v_b_3062_ = v_a_3071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3102_, lean_object* v_str_3103_, lean_object* v_as_3104_, lean_object* v_sz_3105_, lean_object* v_i_3106_, lean_object* v_b_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
size_t v_sz_boxed_3115_; size_t v_i_boxed_3116_; lean_object* v_res_3117_; 
v_sz_boxed_3115_ = lean_unbox_usize(v_sz_3105_);
lean_dec(v_sz_3105_);
v_i_boxed_3116_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_res_3117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3102_, v_str_3103_, v_as_3104_, v_sz_boxed_3115_, v_i_boxed_3116_, v_b_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_as_3104_);
lean_dec_ref(v_str_3103_);
lean_dec(v___y_3102_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_str_3126_; lean_object* v___y_3128_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_str_3126_ = l_Lean_TSyntax_getDocString(v_docstring_3118_);
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = l_Lean_Syntax_getArg(v_docstring_3118_, v___x_3143_);
v___x_3145_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3144_);
lean_dec(v___x_3144_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_box(0);
v___y_3128_ = v___x_3146_;
goto v___jp_3127_;
}
else
{
lean_object* v_val_3147_; uint8_t v___x_3148_; lean_object* v___x_3149_; 
v_val_3147_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_val_3147_);
lean_dec_ref_known(v___x_3145_, 1);
v___x_3148_ = 0;
v___x_3149_ = l_Lean_SourceInfo_getPos_x3f(v_val_3147_, v___x_3148_);
lean_dec(v_val_3147_);
v___y_3128_ = v___x_3149_;
goto v___jp_3127_;
}
v___jp_3127_:
{
lean_object* v___x_3129_; lean_object* v_fst_3130_; lean_object* v___x_3131_; size_t v_sz_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
lean_inc_ref(v_str_3126_);
v___x_3129_ = l_Lean_rewriteManualLinksCore(v_str_3126_);
v_fst_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_fst_3130_);
lean_dec_ref(v___x_3129_);
v___x_3131_ = lean_box(0);
v_sz_3132_ = lean_array_size(v_fst_3130_);
v___x_3133_ = ((size_t)0ULL);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3128_, v_str_3126_, v_fst_3130_, v_sz_3132_, v___x_3133_, v___x_3131_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v_fst_3130_);
lean_dec_ref(v_str_3126_);
lean_dec(v___y_3128_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3142_);
v___x_3136_ = v___x_3134_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v___x_3134_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3131_);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3131_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
return v___x_3134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v_docstring_3150_);
return v_res_3158_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3161_ = l_Lean_stringToMessageData(v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_val_3177_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = l_Lean_Syntax_getArg(v_stx_3162_, v___x_3184_);
switch(lean_obj_tag(v___x_3185_))
{
case 2:
{
lean_object* v_val_3186_; 
lean_dec(v_stx_3162_);
v_val_3186_ = lean_ctor_get(v___x_3185_, 1);
lean_inc_ref(v_val_3186_);
lean_dec_ref_known(v___x_3185_, 2);
v_val_3177_ = v_val_3186_;
goto v___jp_3176_;
}
case 1:
{
lean_object* v_kind_3187_; 
v_kind_3187_ = lean_ctor_get(v___x_3185_, 1);
lean_inc(v_kind_3187_);
if (lean_obj_tag(v_kind_3187_) == 1)
{
lean_object* v_pre_3188_; 
v_pre_3188_ = lean_ctor_get(v_kind_3187_, 0);
lean_inc(v_pre_3188_);
if (lean_obj_tag(v_pre_3188_) == 1)
{
lean_object* v_pre_3189_; 
v_pre_3189_ = lean_ctor_get(v_pre_3188_, 0);
lean_inc(v_pre_3189_);
if (lean_obj_tag(v_pre_3189_) == 1)
{
lean_object* v_pre_3190_; 
v_pre_3190_ = lean_ctor_get(v_pre_3189_, 0);
lean_inc(v_pre_3190_);
if (lean_obj_tag(v_pre_3190_) == 1)
{
lean_object* v_pre_3191_; 
v_pre_3191_ = lean_ctor_get(v_pre_3190_, 0);
if (lean_obj_tag(v_pre_3191_) == 0)
{
lean_object* v_str_3192_; lean_object* v_str_3193_; lean_object* v_str_3194_; lean_object* v_str_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_str_3192_ = lean_ctor_get(v_kind_3187_, 1);
lean_inc_ref(v_str_3192_);
lean_dec_ref_known(v_kind_3187_, 2);
v_str_3193_ = lean_ctor_get(v_pre_3188_, 1);
lean_inc_ref(v_str_3193_);
lean_dec_ref_known(v_pre_3188_, 2);
v_str_3194_ = lean_ctor_get(v_pre_3189_, 1);
lean_inc_ref(v_str_3194_);
lean_dec_ref_known(v_pre_3189_, 2);
v_str_3195_ = lean_ctor_get(v_pre_3190_, 1);
lean_inc_ref(v_str_3195_);
lean_dec_ref_known(v_pre_3190_, 2);
v___x_3196_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3197_ = lean_string_dec_eq(v_str_3195_, v___x_3196_);
lean_dec_ref(v_str_3195_);
if (v___x_3197_ == 0)
{
lean_dec_ref(v_str_3194_);
lean_dec_ref(v_str_3193_);
lean_dec_ref(v_str_3192_);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
else
{
lean_object* v___x_3198_; uint8_t v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3199_ = lean_string_dec_eq(v_str_3194_, v___x_3198_);
lean_dec_ref(v_str_3194_);
if (v___x_3199_ == 0)
{
lean_dec_ref(v_str_3193_);
lean_dec_ref(v_str_3192_);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
else
{
lean_object* v___x_3200_; uint8_t v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3201_ = lean_string_dec_eq(v_str_3193_, v___x_3200_);
lean_dec_ref(v_str_3193_);
if (v___x_3201_ == 0)
{
lean_dec_ref(v_str_3192_);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
else
{
lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3202_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3203_ = lean_string_dec_eq(v_str_3192_, v___x_3202_);
lean_dec_ref(v_str_3192_);
if (v___x_3203_ == 0)
{
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_unsigned_to_nat(0u);
v___x_3205_ = l_Lean_Syntax_getArg(v___x_3185_, v___x_3204_);
lean_dec_ref_known(v___x_3185_, 3);
if (lean_obj_tag(v___x_3205_) == 2)
{
lean_object* v_val_3206_; 
lean_dec(v_stx_3162_);
v_val_3206_ = lean_ctor_get(v___x_3205_, 1);
lean_inc_ref(v_val_3206_);
lean_dec_ref_known(v___x_3205_, 2);
v_val_3177_ = v_val_3206_;
goto v___jp_3176_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v___x_3205_);
v___x_3207_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3162_);
v___x_3208_ = l_Lean_MessageData_ofSyntax(v_stx_3162_);
v___x_3209_ = l_Lean_indentD(v___x_3208_);
v___x_3210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3207_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3162_, v___x_3210_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v_stx_3162_);
return v___x_3211_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3190_, 2);
lean_dec_ref_known(v_pre_3189_, 2);
lean_dec_ref_known(v_pre_3188_, 2);
lean_dec_ref_known(v_kind_3187_, 2);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
}
else
{
lean_dec_ref_known(v_pre_3189_, 2);
lean_dec(v_pre_3190_);
lean_dec_ref_known(v_pre_3188_, 2);
lean_dec_ref_known(v_kind_3187_, 2);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
}
else
{
lean_dec(v_pre_3189_);
lean_dec_ref_known(v_pre_3188_, 2);
lean_dec_ref_known(v_kind_3187_, 2);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
}
else
{
lean_dec(v_pre_3188_);
lean_dec_ref_known(v_kind_3187_, 2);
lean_dec_ref_known(v___x_3185_, 3);
goto v___jp_3170_;
}
}
else
{
lean_dec_ref_known(v___x_3185_, 3);
lean_dec(v_kind_3187_);
goto v___jp_3170_;
}
}
default: 
{
lean_dec(v___x_3185_);
goto v___jp_3170_;
}
}
v___jp_3170_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3171_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3162_);
v___x_3172_ = l_Lean_MessageData_ofSyntax(v_stx_3162_);
v___x_3173_ = l_Lean_indentD(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3162_, v___x_3174_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v_stx_3162_);
return v___x_3175_;
}
v___jp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = lean_string_utf8_byte_size(v_val_3177_);
v___x_3180_ = lean_unsigned_to_nat(2u);
v___x_3181_ = lean_nat_sub(v___x_3179_, v___x_3180_);
v___x_3182_ = lean_string_utf8_extract(v_val_3177_, v___x_3178_, v___x_3181_);
lean_dec(v___x_3181_);
lean_dec_ref(v_val_3177_);
v___x_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
return v___x_3183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3221_, lean_object* v_docComment_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___x_3293_; 
v___x_3293_ = l_Lean_Name_isAnonymous(v_declName_3221_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v_env_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_st_ref_get(v___y_3228_);
v_env_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_ref(v_env_3295_);
lean_dec(v___x_3294_);
v___x_3296_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3295_, v_declName_3221_);
lean_dec_ref(v_env_3295_);
if (lean_obj_tag(v___x_3296_) == 0)
{
v___y_3231_ = v___y_3223_;
v___y_3232_ = v___y_3224_;
v___y_3233_ = v___y_3225_;
v___y_3234_ = v___y_3226_;
v___y_3235_ = v___y_3227_;
v___y_3236_ = v___y_3228_;
goto v___jp_3230_;
}
else
{
lean_dec_ref_known(v___x_3296_, 1);
if (v___x_3293_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v_docComment_3222_);
v___x_3297_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3298_ = l_Lean_MessageData_ofConstName(v_declName_3221_, v___x_3293_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3301_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
return v___x_3302_;
}
else
{
v___y_3231_ = v___y_3223_;
v___y_3232_ = v___y_3224_;
v___y_3233_ = v___y_3225_;
v___y_3234_ = v___y_3226_;
v___y_3235_ = v___y_3227_;
v___y_3236_ = v___y_3228_;
goto v___jp_3230_;
}
}
}
else
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
lean_dec(v_docComment_3222_);
lean_dec(v_declName_3221_);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
return v___x_3304_;
}
v___jp_3230_:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3222_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref_known(v___x_3237_, 1);
v___x_3238_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3222_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3284_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3284_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3284_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v_env_3244_; lean_object* v_nextMacroScope_3245_; lean_object* v_ngen_3246_; lean_object* v_auxDeclNGen_3247_; lean_object* v_traceState_3248_; lean_object* v_messages_3249_; lean_object* v_infoState_3250_; lean_object* v_snapshotTasks_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3282_; 
v___x_3243_ = lean_st_ref_take(v___y_3236_);
v_env_3244_ = lean_ctor_get(v___x_3243_, 0);
v_nextMacroScope_3245_ = lean_ctor_get(v___x_3243_, 1);
v_ngen_3246_ = lean_ctor_get(v___x_3243_, 2);
v_auxDeclNGen_3247_ = lean_ctor_get(v___x_3243_, 3);
v_traceState_3248_ = lean_ctor_get(v___x_3243_, 4);
v_messages_3249_ = lean_ctor_get(v___x_3243_, 6);
v_infoState_3250_ = lean_ctor_get(v___x_3243_, 7);
v_snapshotTasks_3251_ = lean_ctor_get(v___x_3243_, 8);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v___x_3243_, 5);
lean_dec(v_unused_3283_);
v___x_3253_ = v___x_3243_;
v_isShared_3254_ = v_isSharedCheck_3282_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_snapshotTasks_3251_);
lean_inc(v_infoState_3250_);
lean_inc(v_messages_3249_);
lean_inc(v_traceState_3248_);
lean_inc(v_auxDeclNGen_3247_);
lean_inc(v_ngen_3246_);
lean_inc(v_nextMacroScope_3245_);
lean_inc(v_env_3244_);
lean_dec(v___x_3243_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3282_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3255_ = l_Lean_docStringExt;
v___x_3256_ = l_String_removeLeadingSpaces(v_a_3239_);
v___x_3257_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3255_, v_env_3244_, v_declName_3221_, v___x_3256_);
v___x_3258_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 5, v___x_3258_);
lean_ctor_set(v___x_3253_, 0, v___x_3257_);
v___x_3260_ = v___x_3253_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_nextMacroScope_3245_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_ngen_3246_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_auxDeclNGen_3247_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_traceState_3248_);
lean_ctor_set(v_reuseFailAlloc_3281_, 5, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3281_, 6, v_messages_3249_);
lean_ctor_set(v_reuseFailAlloc_3281_, 7, v_infoState_3250_);
lean_ctor_set(v_reuseFailAlloc_3281_, 8, v_snapshotTasks_3251_);
v___x_3260_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v_mctx_3263_; lean_object* v_zetaDeltaFVarIds_3264_; lean_object* v_postponed_3265_; lean_object* v_diag_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3279_; 
v___x_3261_ = lean_st_ref_set(v___y_3236_, v___x_3260_);
v___x_3262_ = lean_st_ref_take(v___y_3234_);
v_mctx_3263_ = lean_ctor_get(v___x_3262_, 0);
v_zetaDeltaFVarIds_3264_ = lean_ctor_get(v___x_3262_, 2);
v_postponed_3265_ = lean_ctor_get(v___x_3262_, 3);
v_diag_3266_ = lean_ctor_get(v___x_3262_, 4);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v___x_3262_, 1);
lean_dec(v_unused_3280_);
v___x_3268_ = v___x_3262_;
v_isShared_3269_ = v_isSharedCheck_3279_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_diag_3266_);
lean_inc(v_postponed_3265_);
lean_inc(v_zetaDeltaFVarIds_3264_);
lean_inc(v_mctx_3263_);
lean_dec(v___x_3262_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3279_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v___x_3270_);
v___x_3272_ = v___x_3268_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_mctx_3263_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3278_, 2, v_zetaDeltaFVarIds_3264_);
lean_ctor_set(v_reuseFailAlloc_3278_, 3, v_postponed_3265_);
lean_ctor_set(v_reuseFailAlloc_3278_, 4, v_diag_3266_);
v___x_3272_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3273_ = lean_st_ref_set(v___y_3234_, v___x_3272_);
v___x_3274_ = lean_box(0);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3274_);
v___x_3276_ = v___x_3241_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_declName_3221_);
v_a_3285_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3238_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3238_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_dec(v_docComment_3222_);
lean_dec(v_declName_3221_);
return v___x_3237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3305_, lean_object* v_docComment_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3305_, v_docComment_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3315_, lean_object* v_declName_3316_, lean_object* v_binders_3317_, lean_object* v_docComment_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
if (v_isVerso_3315_ == 0)
{
lean_object* v___x_3326_; 
lean_dec(v_binders_3317_);
v___x_3326_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3316_, v_docComment_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
return v___x_3326_;
}
else
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_addVersoDocString(v_declName_3316_, v_binders_3317_, v_docComment_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
return v___x_3327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3328_, lean_object* v_declName_3329_, lean_object* v_binders_3330_, lean_object* v_docComment_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
uint8_t v_isVerso_boxed_3339_; lean_object* v_res_3340_; 
v_isVerso_boxed_3339_ = lean_unbox(v_isVerso_3328_);
v_res_3340_ = l_Lean_addDocStringOf(v_isVerso_boxed_3339_, v_declName_3329_, v_binders_3330_, v_docComment_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3341_, lean_object* v_msgData_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3341_, v_msgData_3342_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3351_, lean_object* v_msgData_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3351_, v_msgData_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v_ref_3351_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3361_, lean_object* v_t_3362_){
_start:
{
if (lean_obj_tag(v_t_3362_) == 0)
{
lean_object* v_k_3363_; lean_object* v_v_3364_; lean_object* v_l_3365_; lean_object* v_r_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_4020_; 
v_k_3363_ = lean_ctor_get(v_t_3362_, 1);
v_v_3364_ = lean_ctor_get(v_t_3362_, 2);
v_l_3365_ = lean_ctor_get(v_t_3362_, 3);
v_r_3366_ = lean_ctor_get(v_t_3362_, 4);
v_isSharedCheck_4020_ = !lean_is_exclusive(v_t_3362_);
if (v_isSharedCheck_4020_ == 0)
{
lean_object* v_unused_4021_; 
v_unused_4021_ = lean_ctor_get(v_t_3362_, 0);
lean_dec(v_unused_4021_);
v___x_3368_ = v_t_3362_;
v_isShared_3369_ = v_isSharedCheck_4020_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_r_3366_);
lean_inc(v_l_3365_);
lean_inc(v_v_3364_);
lean_inc(v_k_3363_);
lean_dec(v_t_3362_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_4020_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
uint8_t v___x_3370_; 
v___x_3370_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3361_, v_k_3363_);
switch(v___x_3370_)
{
case 0:
{
lean_object* v_impl_3371_; lean_object* v___x_3372_; 
v_impl_3371_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3361_, v_l_3365_);
v___x_3372_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3371_) == 0)
{
if (lean_obj_tag(v_r_3366_) == 0)
{
lean_object* v_size_3373_; lean_object* v_size_3374_; lean_object* v_k_3375_; lean_object* v_v_3376_; lean_object* v_l_3377_; lean_object* v_r_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v_size_3373_ = lean_ctor_get(v_impl_3371_, 0);
lean_inc(v_size_3373_);
v_size_3374_ = lean_ctor_get(v_r_3366_, 0);
v_k_3375_ = lean_ctor_get(v_r_3366_, 1);
v_v_3376_ = lean_ctor_get(v_r_3366_, 2);
v_l_3377_ = lean_ctor_get(v_r_3366_, 3);
lean_inc(v_l_3377_);
v_r_3378_ = lean_ctor_get(v_r_3366_, 4);
v___x_3379_ = lean_unsigned_to_nat(3u);
v___x_3380_ = lean_nat_mul(v___x_3379_, v_size_3373_);
v___x_3381_ = lean_nat_dec_lt(v___x_3380_, v_size_3374_);
lean_dec(v___x_3380_);
if (v___x_3381_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
lean_dec(v_l_3377_);
v___x_3382_ = lean_nat_add(v___x_3372_, v_size_3373_);
lean_dec(v_size_3373_);
v___x_3383_ = lean_nat_add(v___x_3382_, v_size_3374_);
lean_dec(v___x_3382_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 3, v_impl_3371_);
lean_ctor_set(v___x_3368_, 0, v___x_3383_);
v___x_3385_ = v___x_3368_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_impl_3371_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_r_3366_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
else
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3450_; 
lean_inc(v_r_3378_);
lean_inc(v_v_3376_);
lean_inc(v_k_3375_);
lean_inc(v_size_3374_);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; lean_object* v_unused_3454_; lean_object* v_unused_3455_; 
v_unused_3451_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_r_3366_, 2);
lean_dec(v_unused_3453_);
v_unused_3454_ = lean_ctor_get(v_r_3366_, 1);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3455_);
v___x_3388_ = v_r_3366_;
v_isShared_3389_ = v_isSharedCheck_3450_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v_r_3366_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3450_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_size_3390_; lean_object* v_k_3391_; lean_object* v_v_3392_; lean_object* v_l_3393_; lean_object* v_r_3394_; lean_object* v_size_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v_size_3390_ = lean_ctor_get(v_l_3377_, 0);
v_k_3391_ = lean_ctor_get(v_l_3377_, 1);
v_v_3392_ = lean_ctor_get(v_l_3377_, 2);
v_l_3393_ = lean_ctor_get(v_l_3377_, 3);
v_r_3394_ = lean_ctor_get(v_l_3377_, 4);
v_size_3395_ = lean_ctor_get(v_r_3378_, 0);
v___x_3396_ = lean_unsigned_to_nat(2u);
v___x_3397_ = lean_nat_mul(v___x_3396_, v_size_3395_);
v___x_3398_ = lean_nat_dec_lt(v_size_3390_, v___x_3397_);
lean_dec(v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3426_; 
lean_inc(v_r_3394_);
lean_inc(v_l_3393_);
lean_inc(v_v_3392_);
lean_inc(v_k_3391_);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_l_3377_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; lean_object* v_unused_3431_; 
v_unused_3427_ = lean_ctor_get(v_l_3377_, 4);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_l_3377_, 3);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_l_3377_, 2);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_l_3377_, 1);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_l_3377_, 0);
lean_dec(v_unused_3431_);
v___x_3400_ = v_l_3377_;
v_isShared_3401_ = v_isSharedCheck_3426_;
goto v_resetjp_3399_;
}
else
{
lean_dec(v_l_3377_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3426_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3416_; 
v___x_3402_ = lean_nat_add(v___x_3372_, v_size_3373_);
lean_dec(v_size_3373_);
v___x_3403_ = lean_nat_add(v___x_3402_, v_size_3374_);
lean_dec(v_size_3374_);
if (lean_obj_tag(v_l_3393_) == 0)
{
lean_object* v_size_3424_; 
v_size_3424_ = lean_ctor_get(v_l_3393_, 0);
lean_inc(v_size_3424_);
v___y_3416_ = v_size_3424_;
goto v___jp_3415_;
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_unsigned_to_nat(0u);
v___y_3416_ = v___x_3425_;
goto v___jp_3415_;
}
v___jp_3404_:
{
lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3408_ = lean_nat_add(v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 4, v_r_3378_);
lean_ctor_set(v___x_3400_, 3, v_r_3394_);
lean_ctor_set(v___x_3400_, 2, v_v_3376_);
lean_ctor_set(v___x_3400_, 1, v_k_3375_);
lean_ctor_set(v___x_3400_, 0, v___x_3408_);
v___x_3410_ = v___x_3400_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_k_3375_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_v_3376_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_r_3394_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_r_3378_);
v___x_3410_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
lean_object* v___x_3412_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v___x_3410_);
lean_ctor_set(v___x_3388_, 3, v___y_3405_);
lean_ctor_set(v___x_3388_, 2, v_v_3392_);
lean_ctor_set(v___x_3388_, 1, v_k_3391_);
lean_ctor_set(v___x_3388_, 0, v___x_3403_);
v___x_3412_ = v___x_3388_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_k_3391_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_v_3392_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v___y_3405_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
v___jp_3415_:
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
v___x_3417_ = lean_nat_add(v___x_3402_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec(v___x_3402_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_l_3393_);
lean_ctor_set(v___x_3368_, 3, v_impl_3371_);
lean_ctor_set(v___x_3368_, 0, v___x_3417_);
v___x_3419_ = v___x_3368_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_impl_3371_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_l_3393_);
v___x_3419_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_nat_add(v___x_3372_, v_size_3395_);
if (lean_obj_tag(v_r_3394_) == 0)
{
lean_object* v_size_3421_; 
v_size_3421_ = lean_ctor_get(v_r_3394_, 0);
lean_inc(v_size_3421_);
v___y_3405_ = v___x_3419_;
v___y_3406_ = v___x_3420_;
v___y_3407_ = v_size_3421_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_unsigned_to_nat(0u);
v___y_3405_ = v___x_3419_;
v___y_3406_ = v___x_3420_;
v___y_3407_ = v___x_3422_;
goto v___jp_3404_;
}
}
}
}
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
lean_del_object(v___x_3368_);
v___x_3432_ = lean_nat_add(v___x_3372_, v_size_3373_);
lean_dec(v_size_3373_);
v___x_3433_ = lean_nat_add(v___x_3432_, v_size_3374_);
lean_dec(v_size_3374_);
v___x_3434_ = lean_nat_add(v___x_3432_, v_size_3390_);
lean_dec(v___x_3432_);
lean_inc_ref(v_impl_3371_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 4, v_l_3377_);
lean_ctor_set(v___x_3388_, 3, v_impl_3371_);
lean_ctor_set(v___x_3388_, 2, v_v_3364_);
lean_ctor_set(v___x_3388_, 1, v_k_3363_);
lean_ctor_set(v___x_3388_, 0, v___x_3434_);
v___x_3436_ = v___x_3388_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_impl_3371_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_l_3377_);
v___x_3436_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
v_isSharedCheck_3443_ = !lean_is_exclusive(v_impl_3371_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; lean_object* v_unused_3445_; lean_object* v_unused_3446_; lean_object* v_unused_3447_; lean_object* v_unused_3448_; 
v_unused_3444_ = lean_ctor_get(v_impl_3371_, 4);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_impl_3371_, 3);
lean_dec(v_unused_3445_);
v_unused_3446_ = lean_ctor_get(v_impl_3371_, 2);
lean_dec(v_unused_3446_);
v_unused_3447_ = lean_ctor_get(v_impl_3371_, 1);
lean_dec(v_unused_3447_);
v_unused_3448_ = lean_ctor_get(v_impl_3371_, 0);
lean_dec(v_unused_3448_);
v___x_3438_ = v_impl_3371_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_dec(v_impl_3371_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 4, v_r_3378_);
lean_ctor_set(v___x_3438_, 3, v___x_3436_);
lean_ctor_set(v___x_3438_, 2, v_v_3376_);
lean_ctor_set(v___x_3438_, 1, v_k_3375_);
lean_ctor_set(v___x_3438_, 0, v___x_3433_);
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_k_3375_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_v_3376_);
lean_ctor_set(v_reuseFailAlloc_3442_, 3, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3442_, 4, v_r_3378_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v_size_3456_ = lean_ctor_get(v_impl_3371_, 0);
lean_inc(v_size_3456_);
v___x_3457_ = lean_nat_add(v___x_3372_, v_size_3456_);
lean_dec(v_size_3456_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 3, v_impl_3371_);
lean_ctor_set(v___x_3368_, 0, v___x_3457_);
v___x_3459_ = v___x_3368_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_impl_3371_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v_r_3366_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
if (lean_obj_tag(v_r_3366_) == 0)
{
lean_object* v_l_3461_; 
v_l_3461_ = lean_ctor_get(v_r_3366_, 3);
lean_inc(v_l_3461_);
if (lean_obj_tag(v_l_3461_) == 0)
{
lean_object* v_r_3462_; 
v_r_3462_ = lean_ctor_get(v_r_3366_, 4);
lean_inc(v_r_3462_);
if (lean_obj_tag(v_r_3462_) == 0)
{
lean_object* v_size_3463_; lean_object* v_k_3464_; lean_object* v_v_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3478_; 
v_size_3463_ = lean_ctor_get(v_r_3366_, 0);
v_k_3464_ = lean_ctor_get(v_r_3366_, 1);
v_v_3465_ = lean_ctor_get(v_r_3366_, 2);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; lean_object* v_unused_3480_; 
v_unused_3479_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3479_);
v_unused_3480_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3480_);
v___x_3467_ = v_r_3366_;
v_isShared_3468_ = v_isSharedCheck_3478_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_v_3465_);
lean_inc(v_k_3464_);
lean_inc(v_size_3463_);
lean_dec(v_r_3366_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3478_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v_size_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v_size_3469_ = lean_ctor_get(v_l_3461_, 0);
v___x_3470_ = lean_nat_add(v___x_3372_, v_size_3463_);
lean_dec(v_size_3463_);
v___x_3471_ = lean_nat_add(v___x_3372_, v_size_3469_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 4, v_l_3461_);
lean_ctor_set(v___x_3467_, 3, v_impl_3371_);
lean_ctor_set(v___x_3467_, 2, v_v_3364_);
lean_ctor_set(v___x_3467_, 1, v_k_3363_);
lean_ctor_set(v___x_3467_, 0, v___x_3471_);
v___x_3473_ = v___x_3467_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_impl_3371_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_l_3461_);
v___x_3473_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3475_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_r_3462_);
lean_ctor_set(v___x_3368_, 3, v___x_3473_);
lean_ctor_set(v___x_3368_, 2, v_v_3465_);
lean_ctor_set(v___x_3368_, 1, v_k_3464_);
lean_ctor_set(v___x_3368_, 0, v___x_3470_);
v___x_3475_ = v___x_3368_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_k_3464_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_v_3465_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v_r_3462_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_k_3481_; lean_object* v_v_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3505_; 
v_k_3481_ = lean_ctor_get(v_r_3366_, 1);
v_v_3482_ = lean_ctor_get(v_r_3366_, 2);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; lean_object* v_unused_3507_; lean_object* v_unused_3508_; 
v_unused_3506_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3506_);
v_unused_3507_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3507_);
v_unused_3508_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3508_);
v___x_3484_ = v_r_3366_;
v_isShared_3485_ = v_isSharedCheck_3505_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_v_3482_);
lean_inc(v_k_3481_);
lean_dec(v_r_3366_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3505_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_k_3486_; lean_object* v_v_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3501_; 
v_k_3486_ = lean_ctor_get(v_l_3461_, 1);
v_v_3487_ = lean_ctor_get(v_l_3461_, 2);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_l_3461_);
if (v_isSharedCheck_3501_ == 0)
{
lean_object* v_unused_3502_; lean_object* v_unused_3503_; lean_object* v_unused_3504_; 
v_unused_3502_ = lean_ctor_get(v_l_3461_, 4);
lean_dec(v_unused_3502_);
v_unused_3503_ = lean_ctor_get(v_l_3461_, 3);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_l_3461_, 0);
lean_dec(v_unused_3504_);
v___x_3489_ = v_l_3461_;
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_v_3487_);
lean_inc(v_k_3486_);
lean_dec(v_l_3461_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3501_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
v___x_3491_ = lean_unsigned_to_nat(3u);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 4, v_r_3462_);
lean_ctor_set(v___x_3489_, 3, v_r_3462_);
lean_ctor_set(v___x_3489_, 2, v_v_3364_);
lean_ctor_set(v___x_3489_, 1, v_k_3363_);
lean_ctor_set(v___x_3489_, 0, v___x_3372_);
v___x_3493_ = v___x_3489_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_r_3462_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v_r_3462_);
v___x_3493_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 3, v_r_3462_);
lean_ctor_set(v___x_3484_, 0, v___x_3372_);
v___x_3495_ = v___x_3484_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_k_3481_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_v_3482_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_r_3462_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_r_3462_);
v___x_3495_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3497_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3495_);
lean_ctor_set(v___x_3368_, 3, v___x_3493_);
lean_ctor_set(v___x_3368_, 2, v_v_3487_);
lean_ctor_set(v___x_3368_, 1, v_k_3486_);
lean_ctor_set(v___x_3368_, 0, v___x_3491_);
v___x_3497_ = v___x_3368_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_k_3486_);
lean_ctor_set(v_reuseFailAlloc_3498_, 2, v_v_3487_);
lean_ctor_set(v_reuseFailAlloc_3498_, 3, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3498_, 4, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3509_; 
v_r_3509_ = lean_ctor_get(v_r_3366_, 4);
lean_inc(v_r_3509_);
if (lean_obj_tag(v_r_3509_) == 0)
{
lean_object* v_k_3510_; lean_object* v_v_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3522_; 
v_k_3510_ = lean_ctor_get(v_r_3366_, 1);
v_v_3511_ = lean_ctor_get(v_r_3366_, 2);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; lean_object* v_unused_3524_; lean_object* v_unused_3525_; 
v_unused_3523_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3523_);
v_unused_3524_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3524_);
v_unused_3525_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3525_);
v___x_3513_ = v_r_3366_;
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
lean_dec(v_r_3366_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3522_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3515_ = lean_unsigned_to_nat(3u);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v_l_3461_);
lean_ctor_set(v___x_3513_, 2, v_v_3364_);
lean_ctor_set(v___x_3513_, 1, v_k_3363_);
lean_ctor_set(v___x_3513_, 0, v___x_3372_);
v___x_3517_ = v___x_3513_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_l_3461_);
lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_l_3461_);
v___x_3517_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3519_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_r_3509_);
lean_ctor_set(v___x_3368_, 3, v___x_3517_);
lean_ctor_set(v___x_3368_, 2, v_v_3511_);
lean_ctor_set(v___x_3368_, 1, v_k_3510_);
lean_ctor_set(v___x_3368_, 0, v___x_3515_);
v___x_3519_ = v___x_3368_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3520_, 3, v___x_3517_);
lean_ctor_set(v_reuseFailAlloc_3520_, 4, v_r_3509_);
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
else
{
lean_object* v_size_3526_; lean_object* v_k_3527_; lean_object* v_v_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3539_; 
v_size_3526_ = lean_ctor_get(v_r_3366_, 0);
v_k_3527_ = lean_ctor_get(v_r_3366_, 1);
v_v_3528_ = lean_ctor_get(v_r_3366_, 2);
v_isSharedCheck_3539_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; lean_object* v_unused_3541_; 
v_unused_3540_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3540_);
v_unused_3541_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3541_);
v___x_3530_ = v_r_3366_;
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_v_3528_);
lean_inc(v_k_3527_);
lean_inc(v_size_3526_);
lean_dec(v_r_3366_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3539_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 3, v_r_3509_);
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_size_3526_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3527_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3528_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_r_3509_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_r_3509_);
v___x_3533_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3534_ = lean_unsigned_to_nat(2u);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3533_);
lean_ctor_set(v___x_3368_, 3, v_r_3509_);
lean_ctor_set(v___x_3368_, 0, v___x_3534_);
v___x_3536_ = v___x_3368_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_r_3509_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v___x_3533_);
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
else
{
lean_object* v___x_3543_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 3, v_r_3366_);
lean_ctor_set(v___x_3368_, 0, v___x_3372_);
v___x_3543_ = v___x_3368_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v_r_3366_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_r_3366_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3368_);
lean_dec(v_v_3364_);
lean_dec(v_k_3363_);
if (lean_obj_tag(v_l_3365_) == 0)
{
if (lean_obj_tag(v_r_3366_) == 0)
{
lean_object* v_size_3545_; lean_object* v_k_3546_; lean_object* v_v_3547_; lean_object* v_l_3548_; lean_object* v_r_3549_; lean_object* v_size_3550_; lean_object* v_k_3551_; lean_object* v_v_3552_; lean_object* v_l_3553_; lean_object* v_r_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_size_3545_ = lean_ctor_get(v_l_3365_, 0);
v_k_3546_ = lean_ctor_get(v_l_3365_, 1);
v_v_3547_ = lean_ctor_get(v_l_3365_, 2);
v_l_3548_ = lean_ctor_get(v_l_3365_, 3);
v_r_3549_ = lean_ctor_get(v_l_3365_, 4);
lean_inc(v_r_3549_);
v_size_3550_ = lean_ctor_get(v_r_3366_, 0);
v_k_3551_ = lean_ctor_get(v_r_3366_, 1);
v_v_3552_ = lean_ctor_get(v_r_3366_, 2);
v_l_3553_ = lean_ctor_get(v_r_3366_, 3);
lean_inc(v_l_3553_);
v_r_3554_ = lean_ctor_get(v_r_3366_, 4);
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_dec_lt(v_size_3545_, v_size_3550_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3692_; 
lean_inc(v_l_3548_);
lean_inc(v_v_3547_);
lean_inc(v_k_3546_);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; lean_object* v_unused_3697_; 
v_unused_3693_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_l_3365_, 2);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_l_3365_, 1);
lean_dec(v_unused_3696_);
v_unused_3697_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3697_);
v___x_3558_ = v_l_3365_;
v_isShared_3559_ = v_isSharedCheck_3692_;
goto v_resetjp_3557_;
}
else
{
lean_dec(v_l_3365_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3692_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v_tree_3561_; 
v___x_3560_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3546_, v_v_3547_, v_l_3548_, v_r_3549_);
v_tree_3561_ = lean_ctor_get(v___x_3560_, 2);
lean_inc(v_tree_3561_);
if (lean_obj_tag(v_tree_3561_) == 0)
{
lean_object* v_k_3562_; lean_object* v_v_3563_; lean_object* v_size_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v_k_3562_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_k_3562_);
v_v_3563_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_v_3563_);
lean_dec_ref(v___x_3560_);
v_size_3564_ = lean_ctor_get(v_tree_3561_, 0);
v___x_3565_ = lean_unsigned_to_nat(3u);
v___x_3566_ = lean_nat_mul(v___x_3565_, v_size_3564_);
v___x_3567_ = lean_nat_dec_lt(v___x_3566_, v_size_3550_);
lean_dec(v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3571_; 
lean_dec(v_l_3553_);
v___x_3568_ = lean_nat_add(v___x_3555_, v_size_3564_);
v___x_3569_ = lean_nat_add(v___x_3568_, v_size_3550_);
lean_dec(v___x_3568_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v_r_3366_);
lean_ctor_set(v___x_3558_, 3, v_tree_3561_);
lean_ctor_set(v___x_3558_, 2, v_v_3563_);
lean_ctor_set(v___x_3558_, 1, v_k_3562_);
lean_ctor_set(v___x_3558_, 0, v___x_3569_);
v___x_3571_ = v___x_3558_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_k_3562_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_v_3563_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_tree_3561_);
lean_ctor_set(v_reuseFailAlloc_3572_, 4, v_r_3366_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
else
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3627_; 
lean_inc(v_r_3554_);
lean_inc(v_v_3552_);
lean_inc(v_k_3551_);
lean_inc(v_size_3550_);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; lean_object* v_unused_3632_; 
v_unused_3628_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_r_3366_, 2);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_r_3366_, 1);
lean_dec(v_unused_3631_);
v_unused_3632_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3632_);
v___x_3574_ = v_r_3366_;
v_isShared_3575_ = v_isSharedCheck_3627_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v_r_3366_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3627_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_size_3576_; lean_object* v_k_3577_; lean_object* v_v_3578_; lean_object* v_l_3579_; lean_object* v_r_3580_; lean_object* v_size_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; uint8_t v___x_3584_; 
v_size_3576_ = lean_ctor_get(v_l_3553_, 0);
v_k_3577_ = lean_ctor_get(v_l_3553_, 1);
v_v_3578_ = lean_ctor_get(v_l_3553_, 2);
v_l_3579_ = lean_ctor_get(v_l_3553_, 3);
v_r_3580_ = lean_ctor_get(v_l_3553_, 4);
v_size_3581_ = lean_ctor_get(v_r_3554_, 0);
v___x_3582_ = lean_unsigned_to_nat(2u);
v___x_3583_ = lean_nat_mul(v___x_3582_, v_size_3581_);
v___x_3584_ = lean_nat_dec_lt(v_size_3576_, v___x_3583_);
lean_dec(v___x_3583_);
if (v___x_3584_ == 0)
{
lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3612_; 
lean_inc(v_r_3580_);
lean_inc(v_l_3579_);
lean_inc(v_v_3578_);
lean_inc(v_k_3577_);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_l_3553_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; lean_object* v_unused_3614_; lean_object* v_unused_3615_; lean_object* v_unused_3616_; lean_object* v_unused_3617_; 
v_unused_3613_ = lean_ctor_get(v_l_3553_, 4);
lean_dec(v_unused_3613_);
v_unused_3614_ = lean_ctor_get(v_l_3553_, 3);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_l_3553_, 2);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_l_3553_, 1);
lean_dec(v_unused_3616_);
v_unused_3617_ = lean_ctor_get(v_l_3553_, 0);
lean_dec(v_unused_3617_);
v___x_3586_ = v_l_3553_;
v_isShared_3587_ = v_isSharedCheck_3612_;
goto v_resetjp_3585_;
}
else
{
lean_dec(v_l_3553_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3612_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3602_; 
v___x_3588_ = lean_nat_add(v___x_3555_, v_size_3564_);
v___x_3589_ = lean_nat_add(v___x_3588_, v_size_3550_);
lean_dec(v_size_3550_);
if (lean_obj_tag(v_l_3579_) == 0)
{
lean_object* v_size_3610_; 
v_size_3610_ = lean_ctor_get(v_l_3579_, 0);
lean_inc(v_size_3610_);
v___y_3602_ = v_size_3610_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_unsigned_to_nat(0u);
v___y_3602_ = v___x_3611_;
goto v___jp_3601_;
}
v___jp_3590_:
{
lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3594_ = lean_nat_add(v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec(v___y_3592_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 4, v_r_3554_);
lean_ctor_set(v___x_3586_, 3, v_r_3580_);
lean_ctor_set(v___x_3586_, 2, v_v_3552_);
lean_ctor_set(v___x_3586_, 1, v_k_3551_);
lean_ctor_set(v___x_3586_, 0, v___x_3594_);
v___x_3596_ = v___x_3586_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_r_3580_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_r_3554_);
v___x_3596_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 4, v___x_3596_);
lean_ctor_set(v___x_3574_, 3, v___y_3591_);
lean_ctor_set(v___x_3574_, 2, v_v_3578_);
lean_ctor_set(v___x_3574_, 1, v_k_3577_);
lean_ctor_set(v___x_3574_, 0, v___x_3589_);
v___x_3598_ = v___x_3574_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3577_);
lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3578_);
lean_ctor_set(v_reuseFailAlloc_3599_, 3, v___y_3591_);
lean_ctor_set(v_reuseFailAlloc_3599_, 4, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
v___jp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3603_ = lean_nat_add(v___x_3588_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec(v___x_3588_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v_l_3579_);
lean_ctor_set(v___x_3558_, 3, v_tree_3561_);
lean_ctor_set(v___x_3558_, 2, v_v_3563_);
lean_ctor_set(v___x_3558_, 1, v_k_3562_);
lean_ctor_set(v___x_3558_, 0, v___x_3603_);
v___x_3605_ = v___x_3558_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3562_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3563_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_tree_3561_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_l_3579_);
v___x_3605_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_nat_add(v___x_3555_, v_size_3581_);
if (lean_obj_tag(v_r_3580_) == 0)
{
lean_object* v_size_3607_; 
v_size_3607_ = lean_ctor_get(v_r_3580_, 0);
lean_inc(v_size_3607_);
v___y_3591_ = v___x_3605_;
v___y_3592_ = v___x_3606_;
v___y_3593_ = v_size_3607_;
goto v___jp_3590_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_unsigned_to_nat(0u);
v___y_3591_ = v___x_3605_;
v___y_3592_ = v___x_3606_;
v___y_3593_ = v___x_3608_;
goto v___jp_3590_;
}
}
}
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
v___x_3618_ = lean_nat_add(v___x_3555_, v_size_3564_);
v___x_3619_ = lean_nat_add(v___x_3618_, v_size_3550_);
lean_dec(v_size_3550_);
v___x_3620_ = lean_nat_add(v___x_3618_, v_size_3576_);
lean_dec(v___x_3618_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 4, v_l_3553_);
lean_ctor_set(v___x_3574_, 3, v_tree_3561_);
lean_ctor_set(v___x_3574_, 2, v_v_3563_);
lean_ctor_set(v___x_3574_, 1, v_k_3562_);
lean_ctor_set(v___x_3574_, 0, v___x_3620_);
v___x_3622_ = v___x_3574_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3562_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3563_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_tree_3561_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_l_3553_);
v___x_3622_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3624_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v_r_3554_);
lean_ctor_set(v___x_3558_, 3, v___x_3622_);
lean_ctor_set(v___x_3558_, 2, v_v_3552_);
lean_ctor_set(v___x_3558_, 1, v_k_3551_);
lean_ctor_set(v___x_3558_, 0, v___x_3619_);
v___x_3624_ = v___x_3558_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v___x_3622_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_r_3554_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
}
else
{
lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3686_; 
lean_inc(v_r_3554_);
lean_inc(v_v_3552_);
lean_inc(v_k_3551_);
lean_inc(v_size_3550_);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; lean_object* v_unused_3688_; lean_object* v_unused_3689_; lean_object* v_unused_3690_; lean_object* v_unused_3691_; 
v_unused_3687_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3687_);
v_unused_3688_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3688_);
v_unused_3689_ = lean_ctor_get(v_r_3366_, 2);
lean_dec(v_unused_3689_);
v_unused_3690_ = lean_ctor_get(v_r_3366_, 1);
lean_dec(v_unused_3690_);
v_unused_3691_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3691_);
v___x_3634_ = v_r_3366_;
v_isShared_3635_ = v_isSharedCheck_3686_;
goto v_resetjp_3633_;
}
else
{
lean_dec(v_r_3366_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3686_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
if (lean_obj_tag(v_l_3553_) == 0)
{
if (lean_obj_tag(v_r_3554_) == 0)
{
lean_object* v_k_3636_; lean_object* v_v_3637_; lean_object* v_size_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3642_; 
v_k_3636_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_k_3636_);
v_v_3637_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_v_3637_);
lean_dec_ref(v___x_3560_);
v_size_3638_ = lean_ctor_get(v_l_3553_, 0);
v___x_3639_ = lean_nat_add(v___x_3555_, v_size_3550_);
lean_dec(v_size_3550_);
v___x_3640_ = lean_nat_add(v___x_3555_, v_size_3638_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v_l_3553_);
lean_ctor_set(v___x_3634_, 3, v_tree_3561_);
lean_ctor_set(v___x_3634_, 2, v_v_3637_);
lean_ctor_set(v___x_3634_, 1, v_k_3636_);
lean_ctor_set(v___x_3634_, 0, v___x_3640_);
v___x_3642_ = v___x_3634_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_k_3636_);
lean_ctor_set(v_reuseFailAlloc_3646_, 2, v_v_3637_);
lean_ctor_set(v_reuseFailAlloc_3646_, 3, v_tree_3561_);
lean_ctor_set(v_reuseFailAlloc_3646_, 4, v_l_3553_);
v___x_3642_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3644_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v_r_3554_);
lean_ctor_set(v___x_3558_, 3, v___x_3642_);
lean_ctor_set(v___x_3558_, 2, v_v_3552_);
lean_ctor_set(v___x_3558_, 1, v_k_3551_);
lean_ctor_set(v___x_3558_, 0, v___x_3639_);
v___x_3644_ = v___x_3558_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_r_3554_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
else
{
lean_object* v_k_3647_; lean_object* v_v_3648_; lean_object* v_k_3649_; lean_object* v_v_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3664_; 
lean_dec(v_size_3550_);
v_k_3647_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_k_3647_);
v_v_3648_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_v_3648_);
lean_dec_ref(v___x_3560_);
v_k_3649_ = lean_ctor_get(v_l_3553_, 1);
v_v_3650_ = lean_ctor_get(v_l_3553_, 2);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_l_3553_);
if (v_isSharedCheck_3664_ == 0)
{
lean_object* v_unused_3665_; lean_object* v_unused_3666_; lean_object* v_unused_3667_; 
v_unused_3665_ = lean_ctor_get(v_l_3553_, 4);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_l_3553_, 3);
lean_dec(v_unused_3666_);
v_unused_3667_ = lean_ctor_get(v_l_3553_, 0);
lean_dec(v_unused_3667_);
v___x_3652_ = v_l_3553_;
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_v_3650_);
lean_inc(v_k_3649_);
lean_dec(v_l_3553_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3664_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = lean_unsigned_to_nat(3u);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 4, v_r_3554_);
lean_ctor_set(v___x_3652_, 3, v_r_3554_);
lean_ctor_set(v___x_3652_, 2, v_v_3648_);
lean_ctor_set(v___x_3652_, 1, v_k_3647_);
lean_ctor_set(v___x_3652_, 0, v___x_3555_);
v___x_3656_ = v___x_3652_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_k_3647_);
lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_v_3648_);
lean_ctor_set(v_reuseFailAlloc_3663_, 3, v_r_3554_);
lean_ctor_set(v_reuseFailAlloc_3663_, 4, v_r_3554_);
v___x_3656_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v_r_3554_);
lean_ctor_set(v___x_3634_, 0, v___x_3555_);
v___x_3658_ = v___x_3634_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3662_, 3, v_r_3554_);
lean_ctor_set(v_reuseFailAlloc_3662_, 4, v_r_3554_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v___x_3658_);
lean_ctor_set(v___x_3558_, 3, v___x_3656_);
lean_ctor_set(v___x_3558_, 2, v_v_3650_);
lean_ctor_set(v___x_3558_, 1, v_k_3649_);
lean_ctor_set(v___x_3558_, 0, v___x_3654_);
v___x_3660_ = v___x_3558_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3554_) == 0)
{
lean_object* v_k_3668_; lean_object* v_v_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
lean_dec(v_size_3550_);
v_k_3668_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_k_3668_);
v_v_3669_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_v_3669_);
lean_dec_ref(v___x_3560_);
v___x_3670_ = lean_unsigned_to_nat(3u);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v_l_3553_);
lean_ctor_set(v___x_3634_, 2, v_v_3669_);
lean_ctor_set(v___x_3634_, 1, v_k_3668_);
lean_ctor_set(v___x_3634_, 0, v___x_3555_);
v___x_3672_ = v___x_3634_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3553_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_l_3553_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v_r_3554_);
lean_ctor_set(v___x_3558_, 3, v___x_3672_);
lean_ctor_set(v___x_3558_, 2, v_v_3552_);
lean_ctor_set(v___x_3558_, 1, v_k_3551_);
lean_ctor_set(v___x_3558_, 0, v___x_3670_);
v___x_3674_ = v___x_3558_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3554_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
else
{
lean_object* v_k_3677_; lean_object* v_v_3678_; lean_object* v___x_3680_; 
v_k_3677_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_k_3677_);
v_v_3678_ = lean_ctor_get(v___x_3560_, 1);
lean_inc(v_v_3678_);
lean_dec_ref(v___x_3560_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v_r_3554_);
v___x_3680_ = v___x_3634_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_size_3550_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_k_3551_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v_v_3552_);
lean_ctor_set(v_reuseFailAlloc_3685_, 3, v_r_3554_);
lean_ctor_set(v_reuseFailAlloc_3685_, 4, v_r_3554_);
v___x_3680_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_unsigned_to_nat(2u);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 4, v___x_3680_);
lean_ctor_set(v___x_3558_, 3, v_r_3554_);
lean_ctor_set(v___x_3558_, 2, v_v_3678_);
lean_ctor_set(v___x_3558_, 1, v_k_3677_);
lean_ctor_set(v___x_3558_, 0, v___x_3681_);
v___x_3683_ = v___x_3558_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_k_3677_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_v_3678_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_r_3554_);
lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3680_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
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
lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3850_; 
lean_inc(v_r_3554_);
lean_inc(v_v_3552_);
lean_inc(v_k_3551_);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_r_3366_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; lean_object* v_unused_3852_; lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; 
v_unused_3851_ = lean_ctor_get(v_r_3366_, 4);
lean_dec(v_unused_3851_);
v_unused_3852_ = lean_ctor_get(v_r_3366_, 3);
lean_dec(v_unused_3852_);
v_unused_3853_ = lean_ctor_get(v_r_3366_, 2);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_r_3366_, 1);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_r_3366_, 0);
lean_dec(v_unused_3855_);
v___x_3699_ = v_r_3366_;
v_isShared_3700_ = v_isSharedCheck_3850_;
goto v_resetjp_3698_;
}
else
{
lean_dec(v_r_3366_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3850_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3701_; lean_object* v_tree_3702_; 
v___x_3701_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3551_, v_v_3552_, v_l_3553_, v_r_3554_);
v_tree_3702_ = lean_ctor_get(v___x_3701_, 2);
lean_inc(v_tree_3702_);
if (lean_obj_tag(v_tree_3702_) == 0)
{
lean_object* v_k_3703_; lean_object* v_v_3704_; lean_object* v_size_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_k_3703_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_k_3703_);
v_v_3704_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_v_3704_);
lean_dec_ref(v___x_3701_);
v_size_3705_ = lean_ctor_get(v_tree_3702_, 0);
v___x_3706_ = lean_unsigned_to_nat(3u);
v___x_3707_ = lean_nat_mul(v___x_3706_, v_size_3705_);
v___x_3708_ = lean_nat_dec_lt(v___x_3707_, v_size_3545_);
lean_dec(v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_dec(v_r_3549_);
v___x_3709_ = lean_nat_add(v___x_3555_, v_size_3545_);
v___x_3710_ = lean_nat_add(v___x_3709_, v_size_3705_);
lean_dec(v___x_3709_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_tree_3702_);
lean_ctor_set(v___x_3699_, 3, v_l_3365_);
lean_ctor_set(v___x_3699_, 2, v_v_3704_);
lean_ctor_set(v___x_3699_, 1, v_k_3703_);
lean_ctor_set(v___x_3699_, 0, v___x_3710_);
v___x_3712_ = v___x_3699_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3703_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3704_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_tree_3702_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
else
{
lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3779_; 
lean_inc(v_l_3548_);
lean_inc(v_v_3547_);
lean_inc(v_k_3546_);
lean_inc(v_size_3545_);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; lean_object* v_unused_3781_; lean_object* v_unused_3782_; lean_object* v_unused_3783_; lean_object* v_unused_3784_; 
v_unused_3780_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3781_);
v_unused_3782_ = lean_ctor_get(v_l_3365_, 2);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_l_3365_, 1);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3784_);
v___x_3715_ = v_l_3365_;
v_isShared_3716_ = v_isSharedCheck_3779_;
goto v_resetjp_3714_;
}
else
{
lean_dec(v_l_3365_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3779_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_size_3717_; lean_object* v_size_3718_; lean_object* v_k_3719_; lean_object* v_v_3720_; lean_object* v_l_3721_; lean_object* v_r_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v_size_3717_ = lean_ctor_get(v_l_3548_, 0);
v_size_3718_ = lean_ctor_get(v_r_3549_, 0);
v_k_3719_ = lean_ctor_get(v_r_3549_, 1);
v_v_3720_ = lean_ctor_get(v_r_3549_, 2);
v_l_3721_ = lean_ctor_get(v_r_3549_, 3);
v_r_3722_ = lean_ctor_get(v_r_3549_, 4);
v___x_3723_ = lean_unsigned_to_nat(2u);
v___x_3724_ = lean_nat_mul(v___x_3723_, v_size_3717_);
v___x_3725_ = lean_nat_dec_lt(v_size_3718_, v___x_3724_);
lean_dec(v___x_3724_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3763_; 
lean_inc(v_r_3722_);
lean_inc(v_l_3721_);
lean_inc(v_v_3720_);
lean_inc(v_k_3719_);
lean_del_object(v___x_3715_);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_r_3549_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; 
v_unused_3764_ = lean_ctor_get(v_r_3549_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_r_3549_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_r_3549_, 2);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_r_3549_, 1);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_r_3549_, 0);
lean_dec(v_unused_3768_);
v___x_3727_ = v_r_3549_;
v_isShared_3728_ = v_isSharedCheck_3763_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v_r_3549_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3763_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___x_3751_; lean_object* v___y_3753_; 
v___x_3729_ = lean_nat_add(v___x_3555_, v_size_3545_);
lean_dec(v_size_3545_);
v___x_3730_ = lean_nat_add(v___x_3729_, v_size_3705_);
lean_dec(v___x_3729_);
v___x_3751_ = lean_nat_add(v___x_3555_, v_size_3717_);
if (lean_obj_tag(v_l_3721_) == 0)
{
lean_object* v_size_3761_; 
v_size_3761_ = lean_ctor_get(v_l_3721_, 0);
lean_inc(v_size_3761_);
v___y_3753_ = v_size_3761_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3762_; 
v___x_3762_ = lean_unsigned_to_nat(0u);
v___y_3753_ = v___x_3762_;
goto v___jp_3752_;
}
v___jp_3731_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = lean_nat_add(v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec(v___y_3733_);
lean_inc_ref(v_tree_3702_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 4, v_tree_3702_);
lean_ctor_set(v___x_3727_, 3, v_r_3722_);
lean_ctor_set(v___x_3727_, 2, v_v_3704_);
lean_ctor_set(v___x_3727_, 1, v_k_3703_);
lean_ctor_set(v___x_3727_, 0, v___x_3735_);
v___x_3737_ = v___x_3727_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_k_3703_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_v_3704_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_r_3722_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_tree_3702_);
v___x_3737_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_isSharedCheck_3744_ = !lean_is_exclusive(v_tree_3702_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3745_ = lean_ctor_get(v_tree_3702_, 4);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_tree_3702_, 3);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_tree_3702_, 2);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_tree_3702_, 1);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_tree_3702_, 0);
lean_dec(v_unused_3749_);
v___x_3739_ = v_tree_3702_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_dec(v_tree_3702_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 4, v___x_3737_);
lean_ctor_set(v___x_3739_, 3, v___y_3732_);
lean_ctor_set(v___x_3739_, 2, v_v_3720_);
lean_ctor_set(v___x_3739_, 1, v_k_3719_);
lean_ctor_set(v___x_3739_, 0, v___x_3730_);
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_k_3719_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_v_3720_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v___y_3732_);
lean_ctor_set(v_reuseFailAlloc_3743_, 4, v___x_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
v___jp_3752_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
v___x_3754_ = lean_nat_add(v___x_3751_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec(v___x_3751_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_l_3721_);
lean_ctor_set(v___x_3699_, 3, v_l_3548_);
lean_ctor_set(v___x_3699_, 2, v_v_3547_);
lean_ctor_set(v___x_3699_, 1, v_k_3546_);
lean_ctor_set(v___x_3699_, 0, v___x_3754_);
v___x_3756_ = v___x_3699_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3546_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3547_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_l_3721_);
v___x_3756_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_nat_add(v___x_3555_, v_size_3705_);
if (lean_obj_tag(v_r_3722_) == 0)
{
lean_object* v_size_3758_; 
v_size_3758_ = lean_ctor_get(v_r_3722_, 0);
lean_inc(v_size_3758_);
v___y_3732_ = v___x_3756_;
v___y_3733_ = v___x_3757_;
v___y_3734_ = v_size_3758_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_unsigned_to_nat(0u);
v___y_3732_ = v___x_3756_;
v___y_3733_ = v___x_3757_;
v___y_3734_ = v___x_3759_;
goto v___jp_3731_;
}
}
}
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3769_ = lean_nat_add(v___x_3555_, v_size_3545_);
lean_dec(v_size_3545_);
v___x_3770_ = lean_nat_add(v___x_3769_, v_size_3705_);
lean_dec(v___x_3769_);
v___x_3771_ = lean_nat_add(v___x_3555_, v_size_3705_);
v___x_3772_ = lean_nat_add(v___x_3771_, v_size_3718_);
lean_dec(v___x_3771_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_tree_3702_);
lean_ctor_set(v___x_3699_, 3, v_r_3549_);
lean_ctor_set(v___x_3699_, 2, v_v_3704_);
lean_ctor_set(v___x_3699_, 1, v_k_3703_);
lean_ctor_set(v___x_3699_, 0, v___x_3772_);
v___x_3774_ = v___x_3699_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_k_3703_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_v_3704_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_r_3549_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_tree_3702_);
v___x_3774_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 4, v___x_3774_);
lean_ctor_set(v___x_3715_, 0, v___x_3770_);
v___x_3776_ = v___x_3715_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_k_3546_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_v_3547_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3548_) == 0)
{
lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3808_; 
lean_inc_ref(v_l_3548_);
lean_inc(v_v_3547_);
lean_inc(v_k_3546_);
lean_inc(v_size_3545_);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; lean_object* v_unused_3813_; 
v_unused_3809_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_l_3365_, 2);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_l_3365_, 1);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3813_);
v___x_3786_ = v_l_3365_;
v_isShared_3787_ = v_isSharedCheck_3808_;
goto v_resetjp_3785_;
}
else
{
lean_dec(v_l_3365_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3808_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
if (lean_obj_tag(v_r_3549_) == 0)
{
lean_object* v_k_3788_; lean_object* v_v_3789_; lean_object* v_size_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
v_k_3788_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_k_3788_);
v_v_3789_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_v_3789_);
lean_dec_ref(v___x_3701_);
v_size_3790_ = lean_ctor_get(v_r_3549_, 0);
v___x_3791_ = lean_nat_add(v___x_3555_, v_size_3545_);
lean_dec(v_size_3545_);
v___x_3792_ = lean_nat_add(v___x_3555_, v_size_3790_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_tree_3702_);
lean_ctor_set(v___x_3699_, 3, v_r_3549_);
lean_ctor_set(v___x_3699_, 2, v_v_3789_);
lean_ctor_set(v___x_3699_, 1, v_k_3788_);
lean_ctor_set(v___x_3699_, 0, v___x_3792_);
v___x_3794_ = v___x_3699_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3788_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3789_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_r_3549_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_tree_3702_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 4, v___x_3794_);
lean_ctor_set(v___x_3786_, 0, v___x_3791_);
v___x_3796_ = v___x_3786_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3546_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3547_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
else
{
lean_object* v_k_3799_; lean_object* v_v_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
lean_dec(v_size_3545_);
v_k_3799_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_k_3799_);
v_v_3800_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_v_3800_);
lean_dec_ref(v___x_3701_);
v___x_3801_ = lean_unsigned_to_nat(3u);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_r_3549_);
lean_ctor_set(v___x_3699_, 3, v_r_3549_);
lean_ctor_set(v___x_3699_, 2, v_v_3800_);
lean_ctor_set(v___x_3699_, 1, v_k_3799_);
lean_ctor_set(v___x_3699_, 0, v___x_3555_);
v___x_3803_ = v___x_3699_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_k_3799_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v_v_3800_);
lean_ctor_set(v_reuseFailAlloc_3807_, 3, v_r_3549_);
lean_ctor_set(v_reuseFailAlloc_3807_, 4, v_r_3549_);
v___x_3803_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3805_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 4, v___x_3803_);
lean_ctor_set(v___x_3786_, 0, v___x_3801_);
v___x_3805_ = v___x_3786_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_k_3546_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_v_3547_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3549_) == 0)
{
lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3838_; 
lean_inc(v_l_3548_);
lean_inc(v_v_3547_);
lean_inc(v_k_3546_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; lean_object* v_unused_3840_; lean_object* v_unused_3841_; lean_object* v_unused_3842_; lean_object* v_unused_3843_; 
v_unused_3839_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_l_3365_, 2);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_l_3365_, 1);
lean_dec(v_unused_3842_);
v_unused_3843_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3843_);
v___x_3815_ = v_l_3365_;
v_isShared_3816_ = v_isSharedCheck_3838_;
goto v_resetjp_3814_;
}
else
{
lean_dec(v_l_3365_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3838_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_k_3819_; lean_object* v_v_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3834_; 
v_k_3817_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_k_3817_);
v_v_3818_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_v_3818_);
lean_dec_ref(v___x_3701_);
v_k_3819_ = lean_ctor_get(v_r_3549_, 1);
v_v_3820_ = lean_ctor_get(v_r_3549_, 2);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_r_3549_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; lean_object* v_unused_3837_; 
v_unused_3835_ = lean_ctor_get(v_r_3549_, 4);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_r_3549_, 3);
lean_dec(v_unused_3836_);
v_unused_3837_ = lean_ctor_get(v_r_3549_, 0);
lean_dec(v_unused_3837_);
v___x_3822_ = v_r_3549_;
v_isShared_3823_ = v_isSharedCheck_3834_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_v_3820_);
lean_inc(v_k_3819_);
lean_dec(v_r_3549_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3834_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = lean_unsigned_to_nat(3u);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 4, v_l_3548_);
lean_ctor_set(v___x_3822_, 3, v_l_3548_);
lean_ctor_set(v___x_3822_, 2, v_v_3547_);
lean_ctor_set(v___x_3822_, 1, v_k_3546_);
lean_ctor_set(v___x_3822_, 0, v___x_3555_);
v___x_3826_ = v___x_3822_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_k_3546_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_v_3547_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v_l_3548_);
v___x_3826_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3828_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_l_3548_);
lean_ctor_set(v___x_3699_, 3, v_l_3548_);
lean_ctor_set(v___x_3699_, 2, v_v_3818_);
lean_ctor_set(v___x_3699_, 1, v_k_3817_);
lean_ctor_set(v___x_3699_, 0, v___x_3555_);
v___x_3828_ = v___x_3699_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_l_3548_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v_l_3548_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 4, v___x_3828_);
lean_ctor_set(v___x_3815_, 3, v___x_3826_);
lean_ctor_set(v___x_3815_, 2, v_v_3820_);
lean_ctor_set(v___x_3815_, 1, v_k_3819_);
lean_ctor_set(v___x_3815_, 0, v___x_3824_);
v___x_3830_ = v___x_3815_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3831_, 1, v_k_3819_);
lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_v_3820_);
lean_ctor_set(v_reuseFailAlloc_3831_, 3, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3831_, 4, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
else
{
lean_object* v_k_3844_; lean_object* v_v_3845_; lean_object* v___x_3846_; lean_object* v___x_3848_; 
v_k_3844_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_k_3844_);
v_v_3845_ = lean_ctor_get(v___x_3701_, 1);
lean_inc(v_v_3845_);
lean_dec_ref(v___x_3701_);
v___x_3846_ = lean_unsigned_to_nat(2u);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v_r_3549_);
lean_ctor_set(v___x_3699_, 3, v_l_3365_);
lean_ctor_set(v___x_3699_, 2, v_v_3845_);
lean_ctor_set(v___x_3699_, 1, v_k_3844_);
lean_ctor_set(v___x_3699_, 0, v___x_3846_);
v___x_3848_ = v___x_3699_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_k_3844_);
lean_ctor_set(v_reuseFailAlloc_3849_, 2, v_v_3845_);
lean_ctor_set(v_reuseFailAlloc_3849_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_3849_, 4, v_r_3549_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
}
}
else
{
return v_l_3365_;
}
}
else
{
return v_r_3366_;
}
}
default: 
{
lean_object* v_impl_3856_; lean_object* v___x_3857_; 
v_impl_3856_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3361_, v_r_3366_);
v___x_3857_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3856_) == 0)
{
if (lean_obj_tag(v_l_3365_) == 0)
{
lean_object* v_size_3858_; lean_object* v_size_3859_; lean_object* v_k_3860_; lean_object* v_v_3861_; lean_object* v_l_3862_; lean_object* v_r_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_size_3858_ = lean_ctor_get(v_impl_3856_, 0);
lean_inc(v_size_3858_);
v_size_3859_ = lean_ctor_get(v_l_3365_, 0);
v_k_3860_ = lean_ctor_get(v_l_3365_, 1);
v_v_3861_ = lean_ctor_get(v_l_3365_, 2);
v_l_3862_ = lean_ctor_get(v_l_3365_, 3);
v_r_3863_ = lean_ctor_get(v_l_3365_, 4);
lean_inc(v_r_3863_);
v___x_3864_ = lean_unsigned_to_nat(3u);
v___x_3865_ = lean_nat_mul(v___x_3864_, v_size_3858_);
v___x_3866_ = lean_nat_dec_lt(v___x_3865_, v_size_3859_);
lean_dec(v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3870_; 
lean_dec(v_r_3863_);
v___x_3867_ = lean_nat_add(v___x_3857_, v_size_3859_);
v___x_3868_ = lean_nat_add(v___x_3867_, v_size_3858_);
lean_dec(v_size_3858_);
lean_dec(v___x_3867_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_impl_3856_);
lean_ctor_set(v___x_3368_, 0, v___x_3868_);
v___x_3870_ = v___x_3368_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_impl_3856_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
else
{
lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3937_; 
lean_inc(v_l_3862_);
lean_inc(v_v_3861_);
lean_inc(v_k_3860_);
lean_inc(v_size_3859_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3938_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3938_);
v_unused_3939_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_l_3365_, 2);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_l_3365_, 1);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3942_);
v___x_3873_ = v_l_3365_;
v_isShared_3874_ = v_isSharedCheck_3937_;
goto v_resetjp_3872_;
}
else
{
lean_dec(v_l_3365_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3937_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v_size_3875_; lean_object* v_size_3876_; lean_object* v_k_3877_; lean_object* v_v_3878_; lean_object* v_l_3879_; lean_object* v_r_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v_size_3875_ = lean_ctor_get(v_l_3862_, 0);
v_size_3876_ = lean_ctor_get(v_r_3863_, 0);
v_k_3877_ = lean_ctor_get(v_r_3863_, 1);
v_v_3878_ = lean_ctor_get(v_r_3863_, 2);
v_l_3879_ = lean_ctor_get(v_r_3863_, 3);
v_r_3880_ = lean_ctor_get(v_r_3863_, 4);
v___x_3881_ = lean_unsigned_to_nat(2u);
v___x_3882_ = lean_nat_mul(v___x_3881_, v_size_3875_);
v___x_3883_ = lean_nat_dec_lt(v_size_3876_, v___x_3882_);
lean_dec(v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3912_; 
lean_inc(v_r_3880_);
lean_inc(v_l_3879_);
lean_inc(v_v_3878_);
lean_inc(v_k_3877_);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_r_3863_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3913_ = lean_ctor_get(v_r_3863_, 4);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_r_3863_, 3);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_r_3863_, 2);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_r_3863_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_r_3863_, 0);
lean_dec(v_unused_3917_);
v___x_3885_ = v_r_3863_;
v_isShared_3886_ = v_isSharedCheck_3912_;
goto v_resetjp_3884_;
}
else
{
lean_dec(v_r_3863_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3912_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___x_3900_; lean_object* v___y_3902_; 
v___x_3887_ = lean_nat_add(v___x_3857_, v_size_3859_);
lean_dec(v_size_3859_);
v___x_3888_ = lean_nat_add(v___x_3887_, v_size_3858_);
lean_dec(v___x_3887_);
v___x_3900_ = lean_nat_add(v___x_3857_, v_size_3875_);
if (lean_obj_tag(v_l_3879_) == 0)
{
lean_object* v_size_3910_; 
v_size_3910_ = lean_ctor_get(v_l_3879_, 0);
lean_inc(v_size_3910_);
v___y_3902_ = v_size_3910_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_unsigned_to_nat(0u);
v___y_3902_ = v___x_3911_;
goto v___jp_3901_;
}
v___jp_3889_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_nat_add(v___y_3890_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec(v___y_3890_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 4, v_impl_3856_);
lean_ctor_set(v___x_3885_, 3, v_r_3880_);
lean_ctor_set(v___x_3885_, 2, v_v_3364_);
lean_ctor_set(v___x_3885_, 1, v_k_3363_);
lean_ctor_set(v___x_3885_, 0, v___x_3893_);
v___x_3895_ = v___x_3885_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3899_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3899_, 3, v_r_3880_);
lean_ctor_set(v_reuseFailAlloc_3899_, 4, v_impl_3856_);
v___x_3895_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3897_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 4, v___x_3895_);
lean_ctor_set(v___x_3873_, 3, v___y_3891_);
lean_ctor_set(v___x_3873_, 2, v_v_3878_);
lean_ctor_set(v___x_3873_, 1, v_k_3877_);
lean_ctor_set(v___x_3873_, 0, v___x_3888_);
v___x_3897_ = v___x_3873_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3888_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_k_3877_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_v_3878_);
lean_ctor_set(v_reuseFailAlloc_3898_, 3, v___y_3891_);
lean_ctor_set(v_reuseFailAlloc_3898_, 4, v___x_3895_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
v___jp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_nat_add(v___x_3900_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec(v___x_3900_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_l_3879_);
lean_ctor_set(v___x_3368_, 3, v_l_3862_);
lean_ctor_set(v___x_3368_, 2, v_v_3861_);
lean_ctor_set(v___x_3368_, 1, v_k_3860_);
lean_ctor_set(v___x_3368_, 0, v___x_3903_);
v___x_3905_ = v___x_3368_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_k_3860_);
lean_ctor_set(v_reuseFailAlloc_3909_, 2, v_v_3861_);
lean_ctor_set(v_reuseFailAlloc_3909_, 3, v_l_3862_);
lean_ctor_set(v_reuseFailAlloc_3909_, 4, v_l_3879_);
v___x_3905_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_nat_add(v___x_3857_, v_size_3858_);
lean_dec(v_size_3858_);
if (lean_obj_tag(v_r_3880_) == 0)
{
lean_object* v_size_3907_; 
v_size_3907_ = lean_ctor_get(v_r_3880_, 0);
lean_inc(v_size_3907_);
v___y_3890_ = v___x_3906_;
v___y_3891_ = v___x_3905_;
v___y_3892_ = v_size_3907_;
goto v___jp_3889_;
}
else
{
lean_object* v___x_3908_; 
v___x_3908_ = lean_unsigned_to_nat(0u);
v___y_3890_ = v___x_3906_;
v___y_3891_ = v___x_3905_;
v___y_3892_ = v___x_3908_;
goto v___jp_3889_;
}
}
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_del_object(v___x_3368_);
v___x_3918_ = lean_nat_add(v___x_3857_, v_size_3859_);
lean_dec(v_size_3859_);
v___x_3919_ = lean_nat_add(v___x_3918_, v_size_3858_);
lean_dec(v___x_3918_);
v___x_3920_ = lean_nat_add(v___x_3857_, v_size_3858_);
lean_dec(v_size_3858_);
v___x_3921_ = lean_nat_add(v___x_3920_, v_size_3876_);
lean_dec(v___x_3920_);
lean_inc_ref(v_impl_3856_);
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 4, v_impl_3856_);
lean_ctor_set(v___x_3873_, 3, v_r_3863_);
lean_ctor_set(v___x_3873_, 2, v_v_3364_);
lean_ctor_set(v___x_3873_, 1, v_k_3363_);
lean_ctor_set(v___x_3873_, 0, v___x_3921_);
v___x_3923_ = v___x_3873_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v_r_3863_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v_impl_3856_);
v___x_3923_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
v_isSharedCheck_3930_ = !lean_is_exclusive(v_impl_3856_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; 
v_unused_3931_ = lean_ctor_get(v_impl_3856_, 4);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_impl_3856_, 3);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_impl_3856_, 2);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_impl_3856_, 1);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_impl_3856_, 0);
lean_dec(v_unused_3935_);
v___x_3925_ = v_impl_3856_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v_impl_3856_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 4, v___x_3923_);
lean_ctor_set(v___x_3925_, 3, v_l_3862_);
lean_ctor_set(v___x_3925_, 2, v_v_3861_);
lean_ctor_set(v___x_3925_, 1, v_k_3860_);
lean_ctor_set(v___x_3925_, 0, v___x_3919_);
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_k_3860_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_v_3861_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_l_3862_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v___x_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v_size_3943_ = lean_ctor_get(v_impl_3856_, 0);
lean_inc(v_size_3943_);
v___x_3944_ = lean_nat_add(v___x_3857_, v_size_3943_);
lean_dec(v_size_3943_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_impl_3856_);
lean_ctor_set(v___x_3368_, 0, v___x_3944_);
v___x_3946_ = v___x_3368_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v_impl_3856_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
else
{
if (lean_obj_tag(v_l_3365_) == 0)
{
lean_object* v_l_3948_; 
v_l_3948_ = lean_ctor_get(v_l_3365_, 3);
if (lean_obj_tag(v_l_3948_) == 0)
{
lean_object* v_r_3949_; 
lean_inc_ref(v_l_3948_);
v_r_3949_ = lean_ctor_get(v_l_3365_, 4);
lean_inc(v_r_3949_);
if (lean_obj_tag(v_r_3949_) == 0)
{
lean_object* v_size_3950_; lean_object* v_k_3951_; lean_object* v_v_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3965_; 
v_size_3950_ = lean_ctor_get(v_l_3365_, 0);
v_k_3951_ = lean_ctor_get(v_l_3365_, 1);
v_v_3952_ = lean_ctor_get(v_l_3365_, 2);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; lean_object* v_unused_3967_; 
v_unused_3966_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3966_);
v_unused_3967_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3967_);
v___x_3954_ = v_l_3365_;
v_isShared_3955_ = v_isSharedCheck_3965_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_v_3952_);
lean_inc(v_k_3951_);
lean_inc(v_size_3950_);
lean_dec(v_l_3365_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3965_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v_size_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v_size_3956_ = lean_ctor_get(v_r_3949_, 0);
v___x_3957_ = lean_nat_add(v___x_3857_, v_size_3950_);
lean_dec(v_size_3950_);
v___x_3958_ = lean_nat_add(v___x_3857_, v_size_3956_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 4, v_impl_3856_);
lean_ctor_set(v___x_3954_, 3, v_r_3949_);
lean_ctor_set(v___x_3954_, 2, v_v_3364_);
lean_ctor_set(v___x_3954_, 1, v_k_3363_);
lean_ctor_set(v___x_3954_, 0, v___x_3958_);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_r_3949_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_impl_3856_);
v___x_3960_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3962_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3960_);
lean_ctor_set(v___x_3368_, 3, v_l_3948_);
lean_ctor_set(v___x_3368_, 2, v_v_3952_);
lean_ctor_set(v___x_3368_, 1, v_k_3951_);
lean_ctor_set(v___x_3368_, 0, v___x_3957_);
v___x_3962_ = v___x_3368_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_k_3951_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_v_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v_l_3948_);
lean_ctor_set(v_reuseFailAlloc_3963_, 4, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_k_3968_; lean_object* v_v_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3980_; 
v_k_3968_ = lean_ctor_get(v_l_3365_, 1);
v_v_3969_ = lean_ctor_get(v_l_3365_, 2);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; 
v_unused_3981_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_3983_);
v___x_3971_ = v_l_3365_;
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_v_3969_);
lean_inc(v_k_3968_);
lean_dec(v_l_3365_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_unsigned_to_nat(3u);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 3, v_r_3949_);
lean_ctor_set(v___x_3971_, 2, v_v_3364_);
lean_ctor_set(v___x_3971_, 1, v_k_3363_);
lean_ctor_set(v___x_3971_, 0, v___x_3857_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_r_3949_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_r_3949_);
v___x_3975_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
lean_object* v___x_3977_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3975_);
lean_ctor_set(v___x_3368_, 3, v_l_3948_);
lean_ctor_set(v___x_3368_, 2, v_v_3969_);
lean_ctor_set(v___x_3368_, 1, v_k_3968_);
lean_ctor_set(v___x_3368_, 0, v___x_3973_);
v___x_3977_ = v___x_3368_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3973_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_k_3968_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_v_3969_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_l_3948_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
else
{
lean_object* v_r_3984_; 
v_r_3984_ = lean_ctor_get(v_l_3365_, 4);
lean_inc(v_r_3984_);
if (lean_obj_tag(v_r_3984_) == 0)
{
lean_object* v_k_3985_; lean_object* v_v_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4009_; 
lean_inc(v_l_3948_);
v_k_3985_ = lean_ctor_get(v_l_3365_, 1);
v_v_3986_ = lean_ctor_get(v_l_3365_, 2);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_l_3365_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; lean_object* v_unused_4011_; lean_object* v_unused_4012_; 
v_unused_4010_ = lean_ctor_get(v_l_3365_, 4);
lean_dec(v_unused_4010_);
v_unused_4011_ = lean_ctor_get(v_l_3365_, 3);
lean_dec(v_unused_4011_);
v_unused_4012_ = lean_ctor_get(v_l_3365_, 0);
lean_dec(v_unused_4012_);
v___x_3988_ = v_l_3365_;
v_isShared_3989_ = v_isSharedCheck_4009_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_v_3986_);
lean_inc(v_k_3985_);
lean_dec(v_l_3365_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4009_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v_k_3990_; lean_object* v_v_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4005_; 
v_k_3990_ = lean_ctor_get(v_r_3984_, 1);
v_v_3991_ = lean_ctor_get(v_r_3984_, 2);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_r_3984_);
if (v_isSharedCheck_4005_ == 0)
{
lean_object* v_unused_4006_; lean_object* v_unused_4007_; lean_object* v_unused_4008_; 
v_unused_4006_ = lean_ctor_get(v_r_3984_, 4);
lean_dec(v_unused_4006_);
v_unused_4007_ = lean_ctor_get(v_r_3984_, 3);
lean_dec(v_unused_4007_);
v_unused_4008_ = lean_ctor_get(v_r_3984_, 0);
lean_dec(v_unused_4008_);
v___x_3993_ = v_r_3984_;
v_isShared_3994_ = v_isSharedCheck_4005_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_v_3991_);
lean_inc(v_k_3990_);
lean_dec(v_r_3984_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4005_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3995_ = lean_unsigned_to_nat(3u);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 4, v_l_3948_);
lean_ctor_set(v___x_3993_, 3, v_l_3948_);
lean_ctor_set(v___x_3993_, 2, v_v_3986_);
lean_ctor_set(v___x_3993_, 1, v_k_3985_);
lean_ctor_set(v___x_3993_, 0, v___x_3857_);
v___x_3997_ = v___x_3993_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_k_3985_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_v_3986_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_l_3948_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_l_3948_);
v___x_3997_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3999_; 
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 4, v_l_3948_);
lean_ctor_set(v___x_3988_, 2, v_v_3364_);
lean_ctor_set(v___x_3988_, 1, v_k_3363_);
lean_ctor_set(v___x_3988_, 0, v___x_3857_);
v___x_3999_ = v___x_3988_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_4003_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_4003_, 3, v_l_3948_);
lean_ctor_set(v_reuseFailAlloc_4003_, 4, v_l_3948_);
v___x_3999_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4001_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v___x_3999_);
lean_ctor_set(v___x_3368_, 3, v___x_3997_);
lean_ctor_set(v___x_3368_, 2, v_v_3991_);
lean_ctor_set(v___x_3368_, 1, v_k_3990_);
lean_ctor_set(v___x_3368_, 0, v___x_3995_);
v___x_4001_ = v___x_3368_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_k_3990_);
lean_ctor_set(v_reuseFailAlloc_4002_, 2, v_v_3991_);
lean_ctor_set(v_reuseFailAlloc_4002_, 3, v___x_3997_);
lean_ctor_set(v_reuseFailAlloc_4002_, 4, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4015_; 
v___x_4013_ = lean_unsigned_to_nat(2u);
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_r_3984_);
lean_ctor_set(v___x_3368_, 0, v___x_4013_);
v___x_4015_ = v___x_3368_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_4016_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_4016_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_4016_, 4, v_r_3984_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
else
{
lean_object* v___x_4018_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 4, v_l_3365_);
lean_ctor_set(v___x_3368_, 0, v___x_3857_);
v___x_4018_ = v___x_3368_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v_k_3363_);
lean_ctor_set(v_reuseFailAlloc_4019_, 2, v_v_3364_);
lean_ctor_set(v_reuseFailAlloc_4019_, 3, v_l_3365_);
lean_ctor_set(v_reuseFailAlloc_4019_, 4, v_l_3365_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
}
}
else
{
return v_t_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_4022_, lean_object* v_t_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4022_, v_t_4023_);
lean_dec(v_k_4022_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_4025_, lean_object* v_x_4026_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_4025_, v_x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_4028_, lean_object* v_x_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_4028_, v_x_4029_);
lean_dec(v_declName_4028_);
return v_res_4030_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; lean_object* v_env_4043_; lean_object* v___f_4044_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___x_4088_; 
v___x_4042_ = lean_st_ref_get(v___y_4040_);
v_env_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc_ref(v_env_4043_);
lean_dec(v___x_4042_);
lean_inc(v_declName_4034_);
v___f_4044_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4044_, 0, v_declName_4034_);
v___x_4088_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4043_, v_declName_4034_);
lean_dec_ref(v_env_4043_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_dec(v_declName_4034_);
v___y_4046_ = v___y_4038_;
v___y_4047_ = v___y_4040_;
goto v___jp_4045_;
}
else
{
uint8_t v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec_ref_known(v___x_4088_, 1);
lean_dec_ref(v___f_4044_);
v___x_4089_ = 0;
v___x_4090_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4091_ = l_Lean_MessageData_ofConstName(v_declName_4034_, v___x_4089_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4094_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4095_;
}
v___jp_4045_:
{
lean_object* v___x_4048_; lean_object* v_env_4049_; lean_object* v_nextMacroScope_4050_; lean_object* v_ngen_4051_; lean_object* v_auxDeclNGen_4052_; lean_object* v_traceState_4053_; lean_object* v_messages_4054_; lean_object* v_infoState_4055_; lean_object* v_snapshotTasks_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4086_; 
v___x_4048_ = lean_st_ref_take(v___y_4047_);
v_env_4049_ = lean_ctor_get(v___x_4048_, 0);
v_nextMacroScope_4050_ = lean_ctor_get(v___x_4048_, 1);
v_ngen_4051_ = lean_ctor_get(v___x_4048_, 2);
v_auxDeclNGen_4052_ = lean_ctor_get(v___x_4048_, 3);
v_traceState_4053_ = lean_ctor_get(v___x_4048_, 4);
v_messages_4054_ = lean_ctor_get(v___x_4048_, 6);
v_infoState_4055_ = lean_ctor_get(v___x_4048_, 7);
v_snapshotTasks_4056_ = lean_ctor_get(v___x_4048_, 8);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v___x_4048_, 5);
lean_dec(v_unused_4087_);
v___x_4058_ = v___x_4048_;
v_isShared_4059_ = v_isSharedCheck_4086_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_snapshotTasks_4056_);
lean_inc(v_infoState_4055_);
lean_inc(v_messages_4054_);
lean_inc(v_traceState_4053_);
lean_inc(v_auxDeclNGen_4052_);
lean_inc(v_ngen_4051_);
lean_inc(v_nextMacroScope_4050_);
lean_inc(v_env_4049_);
lean_dec(v___x_4048_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4086_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4060_ = l_Lean_docStringExt;
v___x_4061_ = lean_box(2);
v___x_4062_ = lean_box(0);
v___x_4063_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4060_, v_env_4049_, v___f_4044_, v___x_4061_, v___x_4062_);
v___x_4064_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 5, v___x_4064_);
lean_ctor_set(v___x_4058_, 0, v___x_4063_);
v___x_4066_ = v___x_4058_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_nextMacroScope_4050_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_ngen_4051_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v_auxDeclNGen_4052_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v_traceState_4053_);
lean_ctor_set(v_reuseFailAlloc_4085_, 5, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4085_, 6, v_messages_4054_);
lean_ctor_set(v_reuseFailAlloc_4085_, 7, v_infoState_4055_);
lean_ctor_set(v_reuseFailAlloc_4085_, 8, v_snapshotTasks_4056_);
v___x_4066_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v_mctx_4069_; lean_object* v_zetaDeltaFVarIds_4070_; lean_object* v_postponed_4071_; lean_object* v_diag_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4083_; 
v___x_4067_ = lean_st_ref_set(v___y_4047_, v___x_4066_);
v___x_4068_ = lean_st_ref_take(v___y_4046_);
v_mctx_4069_ = lean_ctor_get(v___x_4068_, 0);
v_zetaDeltaFVarIds_4070_ = lean_ctor_get(v___x_4068_, 2);
v_postponed_4071_ = lean_ctor_get(v___x_4068_, 3);
v_diag_4072_ = lean_ctor_get(v___x_4068_, 4);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v___x_4068_, 1);
lean_dec(v_unused_4084_);
v___x_4074_ = v___x_4068_;
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_diag_4072_);
lean_inc(v_postponed_4071_);
lean_inc(v_zetaDeltaFVarIds_4070_);
lean_inc(v_mctx_4069_);
lean_dec(v___x_4068_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4083_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4076_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4076_);
v___x_4078_ = v___x_4074_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_mctx_4069_);
lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4082_, 2, v_zetaDeltaFVarIds_4070_);
lean_ctor_set(v_reuseFailAlloc_4082_, 3, v_postponed_4071_);
lean_ctor_set(v_reuseFailAlloc_4082_, 4, v_diag_4072_);
v___x_4078_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = lean_st_ref_set(v___y_4046_, v___x_4078_);
v___x_4080_ = lean_box(0);
v___x_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
return v___x_4081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4104_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4107_ = l_Lean_stringToMessageData(v___x_4106_);
return v___x_4107_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4110_ = l_Lean_stringToMessageData(v___x_4109_);
return v___x_4110_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4113_ = l_Lean_stringToMessageData(v___x_4112_);
return v___x_4113_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4116_ = l_Lean_stringToMessageData(v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_){
_start:
{
lean_object* v___x_4125_; lean_object* v_env_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; 
v___x_4125_ = lean_st_ref_get(v_a_4123_);
v_env_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc_ref(v_env_4126_);
lean_dec(v___x_4125_);
v___x_4127_ = 1;
lean_inc(v_declName_4117_);
v___x_4128_ = l_Lean_findInternalDocString_x3f(v_env_4126_, v_declName_4117_, v___x_4127_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
if (lean_obj_tag(v_a_4129_) == 1)
{
lean_object* v_val_4130_; 
v_val_4130_ = lean_ctor_get(v_a_4129_, 0);
lean_inc(v_val_4130_);
lean_dec_ref_known(v_a_4129_, 1);
if (lean_obj_tag(v_val_4130_) == 0)
{
lean_object* v_val_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4153_; 
v_val_4131_ = lean_ctor_get(v_val_4130_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_val_4130_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4133_ = v_val_4130_;
v_isShared_4134_ = v_isSharedCheck_4153_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_val_4131_);
lean_dec(v_val_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4153_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_removeBuiltinDocString(v_declName_4117_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v___x_4136_; 
lean_dec_ref_known(v___x_4135_, 1);
lean_del_object(v___x_4133_);
lean_inc(v_declName_4117_);
v___x_4136_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v___x_4137_; 
lean_dec_ref_known(v___x_4136_, 1);
v___x_4137_ = l_Lean_addVersoDocStringFromString(v_declName_4117_, v_val_4131_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4137_;
}
else
{
lean_dec(v_val_4131_);
lean_dec(v_declName_4117_);
return v___x_4136_;
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_val_4131_);
lean_dec(v_declName_4117_);
v_a_4138_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4140_ = v___x_4135_;
v_isShared_4141_ = v_isSharedCheck_4152_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4135_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4152_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_ref_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v_ref_4142_ = lean_ctor_get(v_a_4122_, 5);
v___x_4143_ = lean_io_error_to_string(v_a_4138_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 3);
lean_ctor_set(v___x_4133_, 0, v___x_4143_);
v___x_4145_ = v___x_4133_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4146_ = l_Lean_MessageData_ofFormat(v___x_4145_);
lean_inc(v_ref_4142_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v_ref_4142_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4147_);
v___x_4149_ = v___x_4140_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
}
}
else
{
lean_object* v___x_4154_; uint8_t v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_dec(v_val_4130_);
v___x_4154_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4155_ = 0;
v___x_4156_ = l_Lean_MessageData_ofConstName(v_declName_4117_, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4154_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4159_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4160_;
}
}
else
{
lean_object* v___x_4161_; uint8_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_dec(v_a_4129_);
v___x_4161_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4162_ = 0;
v___x_4163_ = l_Lean_MessageData_ofConstName(v_declName_4117_, v___x_4162_);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4161_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4164_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4166_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_);
return v___x_4167_;
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v_declName_4117_);
v_a_4168_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4170_ = v___x_4128_;
v_isShared_4171_ = v_isSharedCheck_4180_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4128_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4180_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v_ref_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v_ref_4172_ = lean_ctor_get(v_a_4122_, 5);
v___x_4173_ = lean_io_error_to_string(v_a_4168_);
v___x_4174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
v___x_4175_ = l_Lean_MessageData_ofFormat(v___x_4174_);
lean_inc(v_ref_4172_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_ref_4172_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set(v___x_4170_, 0, v___x_4176_);
v___x_4178_ = v___x_4170_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_makeDocStringVerso(v_declName_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4190_, lean_object* v_k_4191_, lean_object* v_t_4192_, lean_object* v_h_4193_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4191_, v_t_4192_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4195_, lean_object* v_k_4196_, lean_object* v_t_4197_, lean_object* v_h_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4195_, v_k_4196_, v_t_4197_, v_h_4198_);
lean_dec(v_k_4196_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4200_, lean_object* v_binders_4201_, lean_object* v_docComment_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_){
_start:
{
uint8_t v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = l_Lean_isVersoDocComment(v_docComment_4202_);
v___x_4211_ = l_Lean_addDocStringOf(v___x_4210_, v_declName_4200_, v_binders_4201_, v_docComment_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4212_, lean_object* v_binders_4213_, lean_object* v_docComment_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_addDocString(v_declName_4212_, v_binders_4213_, v_docComment_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_);
lean_dec(v_a_4220_);
lean_dec_ref(v_a_4219_);
lean_dec(v_a_4218_);
lean_dec_ref(v_a_4217_);
lean_dec(v_a_4216_);
lean_dec_ref(v_a_4215_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4223_, lean_object* v_binders_4224_, lean_object* v_docString_x3f_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4225_) == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_dec(v_binders_4224_);
lean_dec(v_declName_4223_);
v___x_4233_ = lean_box(0);
v___x_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
return v___x_4234_;
}
else
{
lean_object* v_val_4235_; lean_object* v___x_4236_; 
v_val_4235_ = lean_ctor_get(v_docString_x3f_4225_, 0);
lean_inc(v_val_4235_);
lean_dec_ref_known(v_docString_x3f_4225_, 1);
v___x_4236_ = l_Lean_addDocString(v_declName_4223_, v_binders_4224_, v_val_4235_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
return v___x_4236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4237_, lean_object* v_binders_4238_, lean_object* v_docString_x3f_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l_Lean_addDocString_x27(v_declName_4237_, v_binders_4238_, v_docString_x3f_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v_nextMacroScope_4253_; lean_object* v_ngen_4254_; lean_object* v_auxDeclNGen_4255_; lean_object* v_traceState_4256_; lean_object* v_messages_4257_; lean_object* v_infoState_4258_; lean_object* v_snapshotTasks_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4285_; 
v___x_4252_ = lean_st_ref_take(v___y_4250_);
v_nextMacroScope_4253_ = lean_ctor_get(v___x_4252_, 1);
v_ngen_4254_ = lean_ctor_get(v___x_4252_, 2);
v_auxDeclNGen_4255_ = lean_ctor_get(v___x_4252_, 3);
v_traceState_4256_ = lean_ctor_get(v___x_4252_, 4);
v_messages_4257_ = lean_ctor_get(v___x_4252_, 6);
v_infoState_4258_ = lean_ctor_get(v___x_4252_, 7);
v_snapshotTasks_4259_ = lean_ctor_get(v___x_4252_, 8);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; lean_object* v_unused_4287_; 
v_unused_4286_ = lean_ctor_get(v___x_4252_, 5);
lean_dec(v_unused_4286_);
v_unused_4287_ = lean_ctor_get(v___x_4252_, 0);
lean_dec(v_unused_4287_);
v___x_4261_ = v___x_4252_;
v_isShared_4262_ = v_isSharedCheck_4285_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_snapshotTasks_4259_);
lean_inc(v_infoState_4258_);
lean_inc(v_messages_4257_);
lean_inc(v_traceState_4256_);
lean_inc(v_auxDeclNGen_4255_);
lean_inc(v_ngen_4254_);
lean_inc(v_nextMacroScope_4253_);
lean_dec(v___x_4252_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4285_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
v___x_4263_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4262_ == 0)
{
lean_ctor_set(v___x_4261_, 5, v___x_4263_);
lean_ctor_set(v___x_4261_, 0, v_env_4248_);
v___x_4265_ = v___x_4261_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_env_4248_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_nextMacroScope_4253_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_ngen_4254_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_auxDeclNGen_4255_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_traceState_4256_);
lean_ctor_set(v_reuseFailAlloc_4284_, 5, v___x_4263_);
lean_ctor_set(v_reuseFailAlloc_4284_, 6, v_messages_4257_);
lean_ctor_set(v_reuseFailAlloc_4284_, 7, v_infoState_4258_);
lean_ctor_set(v_reuseFailAlloc_4284_, 8, v_snapshotTasks_4259_);
v___x_4265_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v_mctx_4268_; lean_object* v_zetaDeltaFVarIds_4269_; lean_object* v_postponed_4270_; lean_object* v_diag_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4282_; 
v___x_4266_ = lean_st_ref_set(v___y_4250_, v___x_4265_);
v___x_4267_ = lean_st_ref_take(v___y_4249_);
v_mctx_4268_ = lean_ctor_get(v___x_4267_, 0);
v_zetaDeltaFVarIds_4269_ = lean_ctor_get(v___x_4267_, 2);
v_postponed_4270_ = lean_ctor_get(v___x_4267_, 3);
v_diag_4271_ = lean_ctor_get(v___x_4267_, 4);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4282_ == 0)
{
lean_object* v_unused_4283_; 
v_unused_4283_ = lean_ctor_get(v___x_4267_, 1);
lean_dec(v_unused_4283_);
v___x_4273_ = v___x_4267_;
v_isShared_4274_ = v_isSharedCheck_4282_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_diag_4271_);
lean_inc(v_postponed_4270_);
lean_inc(v_zetaDeltaFVarIds_4269_);
lean_inc(v_mctx_4268_);
lean_dec(v___x_4267_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4282_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4275_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 1, v___x_4275_);
v___x_4277_ = v___x_4273_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_mctx_4268_);
lean_ctor_set(v_reuseFailAlloc_4281_, 1, v___x_4275_);
lean_ctor_set(v_reuseFailAlloc_4281_, 2, v_zetaDeltaFVarIds_4269_);
lean_ctor_set(v_reuseFailAlloc_4281_, 3, v_postponed_4270_);
lean_ctor_set(v_reuseFailAlloc_4281_, 4, v_diag_4271_);
v___x_4277_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
v___x_4278_ = lean_st_ref_set(v___y_4249_, v___x_4277_);
v___x_4279_ = lean_box(0);
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
return v___x_4280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec(v___y_4289_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4293_, lean_object* v_as_4294_, size_t v_i_4295_, size_t v_stop_4296_, lean_object* v_b_4297_){
_start:
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_usize_dec_eq(v_i_4295_, v_stop_4296_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v_index_4300_; lean_object* v_sourceString_4301_; lean_object* v_imports_4302_; lean_object* v_currNamespace_4303_; lean_object* v_openDecls_4304_; lean_object* v_options_4305_; lean_object* v_check_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4322_; 
v___x_4299_ = lean_array_uget(v_as_4294_, v_i_4295_);
v_index_4300_ = lean_ctor_get(v___x_4299_, 1);
v_sourceString_4301_ = lean_ctor_get(v___x_4299_, 2);
v_imports_4302_ = lean_ctor_get(v___x_4299_, 3);
v_currNamespace_4303_ = lean_ctor_get(v___x_4299_, 4);
v_openDecls_4304_ = lean_ctor_get(v___x_4299_, 5);
v_options_4305_ = lean_ctor_get(v___x_4299_, 6);
v_check_4306_ = lean_ctor_get(v___x_4299_, 7);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4322_ == 0)
{
lean_object* v_unused_4323_; 
v_unused_4323_ = lean_ctor_get(v___x_4299_, 0);
lean_dec(v_unused_4323_);
v___x_4308_ = v___x_4299_;
v_isShared_4309_ = v_isSharedCheck_4322_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_check_4306_);
lean_inc(v_options_4305_);
lean_inc(v_openDecls_4304_);
lean_inc(v_currNamespace_4303_);
lean_inc(v_imports_4302_);
lean_inc(v_sourceString_4301_);
lean_inc(v_index_4300_);
lean_dec(v___x_4299_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4322_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4310_; lean_object* v_toEnvExtension_4311_; lean_object* v_asyncMode_4312_; lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4310_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4311_ = lean_ctor_get(v___x_4310_, 0);
v_asyncMode_4312_ = lean_ctor_get(v_toEnvExtension_4311_, 2);
lean_inc(v_n_4293_);
v___x_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_n_4293_);
if (v_isShared_4309_ == 0)
{
lean_ctor_set(v___x_4308_, 0, v___x_4313_);
v___x_4315_ = v___x_4308_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4313_);
lean_ctor_set(v_reuseFailAlloc_4321_, 1, v_index_4300_);
lean_ctor_set(v_reuseFailAlloc_4321_, 2, v_sourceString_4301_);
lean_ctor_set(v_reuseFailAlloc_4321_, 3, v_imports_4302_);
lean_ctor_set(v_reuseFailAlloc_4321_, 4, v_currNamespace_4303_);
lean_ctor_set(v_reuseFailAlloc_4321_, 5, v_openDecls_4304_);
lean_ctor_set(v_reuseFailAlloc_4321_, 6, v_options_4305_);
lean_ctor_set(v_reuseFailAlloc_4321_, 7, v_check_4306_);
v___x_4315_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; size_t v___x_4318_; size_t v___x_4319_; 
v___x_4316_ = lean_box(0);
v___x_4317_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4310_, v_b_4297_, v___x_4315_, v_asyncMode_4312_, v___x_4316_);
v___x_4318_ = ((size_t)1ULL);
v___x_4319_ = lean_usize_add(v_i_4295_, v___x_4318_);
v_i_4295_ = v___x_4319_;
v_b_4297_ = v___x_4317_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4293_);
return v_b_4297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4324_, lean_object* v_as_4325_, lean_object* v_i_4326_, lean_object* v_stop_4327_, lean_object* v_b_4328_){
_start:
{
size_t v_i_boxed_4329_; size_t v_stop_boxed_4330_; lean_object* v_res_4331_; 
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_stop_boxed_4330_ = lean_unbox_usize(v_stop_4327_);
lean_dec(v_stop_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4324_, v_as_4325_, v_i_boxed_4329_, v_stop_boxed_4330_, v_b_4328_);
lean_dec_ref(v_as_4325_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4332_, lean_object* v_deferred_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v___x_4341_; lean_object* v_env_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4341_ = lean_st_ref_get(v___y_4339_);
v_env_4342_ = lean_ctor_get(v___x_4341_, 0);
lean_inc_ref(v_env_4342_);
lean_dec(v___x_4341_);
v___x_4343_ = l_Lean_getMainModuleDoc(v_env_4342_);
v___x_4344_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4343_);
lean_dec_ref(v___x_4343_);
if (v___x_4344_ == 0)
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_dec_ref(v_docs_4332_);
v___x_4345_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4346_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4345_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
return v___x_4346_;
}
else
{
lean_object* v___x_4347_; lean_object* v_env_4348_; lean_object* v___x_4349_; lean_object* v_size_4350_; lean_object* v___x_4351_; lean_object* v_env_4352_; lean_object* v___x_4353_; 
v___x_4347_ = lean_st_ref_get(v___y_4339_);
v_env_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc_ref(v_env_4348_);
lean_dec(v___x_4347_);
v___x_4349_ = l_Lean_getMainVersoModuleDocs(v_env_4348_);
v_size_4350_ = lean_ctor_get(v___x_4349_, 2);
lean_inc(v_size_4350_);
lean_dec_ref(v___x_4349_);
v___x_4351_ = lean_st_ref_get(v___y_4339_);
v_env_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc_ref(v_env_4352_);
lean_dec(v___x_4351_);
v___x_4353_ = l_Lean_addVersoModuleDocSnippet(v_env_4352_, v_docs_4332_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_dec(v_size_4350_);
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4356_ = l_Lean_stringToMessageData(v_a_4354_);
v___x_4357_ = l_Lean_indentD(v___x_4356_);
v___x_4358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4355_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4358_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
return v___x_4359_;
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_a_4360_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4362_ = lean_array_get_size(v_deferred_4333_);
v___x_4363_ = lean_nat_dec_lt(v___x_4361_, v___x_4362_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec(v_size_4350_);
v___x_4364_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4360_, v___y_4337_, v___y_4339_);
return v___x_4364_;
}
else
{
uint8_t v___x_4365_; 
v___x_4365_ = lean_nat_dec_le(v___x_4362_, v___x_4362_);
if (v___x_4365_ == 0)
{
if (v___x_4363_ == 0)
{
lean_object* v___x_4366_; 
lean_dec(v_size_4350_);
v___x_4366_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4360_, v___y_4337_, v___y_4339_);
return v___x_4366_;
}
else
{
size_t v___x_4367_; size_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4367_ = ((size_t)0ULL);
v___x_4368_ = lean_usize_of_nat(v___x_4362_);
v___x_4369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4350_, v_deferred_4333_, v___x_4367_, v___x_4368_, v_a_4360_);
v___x_4370_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4369_, v___y_4337_, v___y_4339_);
return v___x_4370_;
}
}
else
{
size_t v___x_4371_; size_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4371_ = ((size_t)0ULL);
v___x_4372_ = lean_usize_of_nat(v___x_4362_);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4350_, v_deferred_4333_, v___x_4371_, v___x_4372_, v_a_4360_);
v___x_4374_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4373_, v___y_4337_, v___y_4339_);
return v___x_4374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4375_, lean_object* v_deferred_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4375_, v_deferred_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec_ref(v_deferred_4376_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4385_, lean_object* v_docComment_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_versoModDocString(v_range_4385_, v_docComment_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v_fst_4396_; lean_object* v_snd_4397_; lean_object* v___x_4398_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_fst_4396_ = lean_ctor_get(v_a_4395_, 0);
lean_inc(v_fst_4396_);
v_snd_4397_ = lean_ctor_get(v_a_4395_, 1);
lean_inc(v_snd_4397_);
lean_dec(v_a_4395_);
v___x_4398_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4396_, v_snd_4397_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
lean_dec(v_snd_4397_);
return v___x_4398_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
v_a_4399_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4394_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4394_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4407_, lean_object* v_docComment_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l_Lean_addVersoModDocString(v_range_4407_, v_docComment_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
lean_dec(v_a_4414_);
lean_dec_ref(v_a_4413_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_docComment_4408_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4417_, v___y_4421_, v___y_4423_);
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4434_;
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
