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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__0(lean_object* v_toPure_133_, lean_object* v_____r_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_box(0);
v___x_136_ = lean_apply_2(v_toPure_133_, lean_box(0), v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__1(lean_object* v_toPure_137_, lean_object* v_____s_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = lean_box(0);
v___x_140_ = lean_apply_2(v_toPure_137_, lean_box(0), v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__2(lean_object* v___x_141_, lean_object* v_toPure_142_, lean_object* v_____r_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_141_);
v___x_145_ = lean_apply_2(v_toPure_142_, lean_box(0), v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3(lean_object* v_text_147_, lean_object* v_fst_148_, lean_object* v_snd_149_, uint8_t v___x_150_, lean_object* v_logMessage_151_, lean_object* v_toBind_152_, lean_object* v___f_153_, lean_object* v_____do__lift_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_155_ = l_Lean_FileMap_toPosition(v_text_147_, v_fst_148_);
v___x_156_ = lean_box(0);
v___x_157_ = 2;
v___x_158_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_159_ = l_Lean_Parser_Error_toString(v_snd_149_);
v___x_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = l_Lean_MessageData_ofFormat(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_162_, 0, v_____do__lift_154_);
lean_ctor_set(v___x_162_, 1, v___x_155_);
lean_ctor_set(v___x_162_, 2, v___x_156_);
lean_ctor_set(v___x_162_, 3, v___x_158_);
lean_ctor_set(v___x_162_, 4, v___x_161_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*5, v___x_150_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*5 + 1, v___x_157_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*5 + 2, v___x_150_);
v___x_163_ = lean_apply_1(v_logMessage_151_, v___x_162_);
v___x_164_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_163_, v___f_153_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__3___boxed(lean_object* v_text_165_, lean_object* v_fst_166_, lean_object* v_snd_167_, lean_object* v___x_168_, lean_object* v_logMessage_169_, lean_object* v_toBind_170_, lean_object* v___f_171_, lean_object* v_____do__lift_172_){
_start:
{
uint8_t v___x_1474__boxed_173_; lean_object* v_res_174_; 
v___x_1474__boxed_173_ = lean_unbox(v___x_168_);
v_res_174_ = l_Lean_parseVersoDocString___redArg___lam__3(v_text_165_, v_fst_166_, v_snd_167_, v___x_1474__boxed_173_, v_logMessage_169_, v_toBind_170_, v___f_171_, v_____do__lift_172_);
lean_dec(v_fst_166_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4(lean_object* v_text_175_, uint8_t v___x_176_, lean_object* v_logMessage_177_, lean_object* v_toBind_178_, lean_object* v___f_179_, lean_object* v_getFileName_180_, lean_object* v_a_181_, lean_object* v_x_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_snd_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_187_; lean_object* v___f_188_; lean_object* v___x_189_; 
v_snd_184_ = lean_ctor_get(v_a_181_, 1);
lean_inc(v_snd_184_);
v_fst_185_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_fst_185_);
lean_dec_ref(v_a_181_);
v_snd_186_ = lean_ctor_get(v_snd_184_, 1);
lean_inc(v_snd_186_);
lean_dec(v_snd_184_);
v___x_187_ = lean_box(v___x_176_);
lean_inc(v_toBind_178_);
v___f_188_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_188_, 0, v_text_175_);
lean_closure_set(v___f_188_, 1, v_fst_185_);
lean_closure_set(v___f_188_, 2, v_snd_186_);
lean_closure_set(v___f_188_, 3, v___x_187_);
lean_closure_set(v___f_188_, 4, v_logMessage_177_);
lean_closure_set(v___f_188_, 5, v_toBind_178_);
lean_closure_set(v___f_188_, 6, v___f_179_);
v___x_189_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v_getFileName_180_, v___f_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__4___boxed(lean_object* v_text_190_, lean_object* v___x_191_, lean_object* v_logMessage_192_, lean_object* v_toBind_193_, lean_object* v___f_194_, lean_object* v_getFileName_195_, lean_object* v_a_196_, lean_object* v_x_197_, lean_object* v___y_198_){
_start:
{
uint8_t v___x_1508__boxed_199_; lean_object* v_res_200_; 
v___x_1508__boxed_199_ = lean_unbox(v___x_191_);
v_res_200_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_190_, v___x_1508__boxed_199_, v_logMessage_192_, v_toBind_193_, v___f_194_, v_getFileName_195_, v_a_196_, v_x_197_, v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5(lean_object* v_text_203_, lean_object* v_pos_204_, lean_object* v_source_205_, uint8_t v___x_206_, lean_object* v_logMessage_207_, lean_object* v_toBind_208_, lean_object* v___f_209_, lean_object* v_____do__lift_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint32_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_211_ = l_Lean_FileMap_toPosition(v_text_203_, v_pos_204_);
v___x_212_ = lean_box(0);
v___x_213_ = 2;
v___x_214_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_215_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_216_ = lean_string_utf8_get(v_source_205_, v_pos_204_);
v___x_217_ = lean_string_push(v___x_214_, v___x_216_);
v___x_218_ = lean_string_append(v___x_215_, v___x_217_);
lean_dec_ref(v___x_217_);
v___x_219_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_220_ = lean_string_append(v___x_218_, v___x_219_);
v___x_221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofFormat(v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_223_, 0, v_____do__lift_210_);
lean_ctor_set(v___x_223_, 1, v___x_211_);
lean_ctor_set(v___x_223_, 2, v___x_212_);
lean_ctor_set(v___x_223_, 3, v___x_214_);
lean_ctor_set(v___x_223_, 4, v___x_222_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5, v___x_206_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5 + 1, v___x_213_);
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5 + 2, v___x_206_);
v___x_224_ = lean_apply_1(v_logMessage_207_, v___x_223_);
v___x_225_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v___x_224_, v___f_209_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__5___boxed(lean_object* v_text_226_, lean_object* v_pos_227_, lean_object* v_source_228_, lean_object* v___x_229_, lean_object* v_logMessage_230_, lean_object* v_toBind_231_, lean_object* v___f_232_, lean_object* v_____do__lift_233_){
_start:
{
uint8_t v___x_1538__boxed_234_; lean_object* v_res_235_; 
v___x_1538__boxed_234_ = lean_unbox(v___x_229_);
v_res_235_ = l_Lean_parseVersoDocString___redArg___lam__5(v_text_226_, v_pos_227_, v_source_228_, v___x_1538__boxed_234_, v_logMessage_230_, v_toBind_231_, v___f_232_, v_____do__lift_233_);
lean_dec_ref(v_source_228_);
lean_dec(v_pos_227_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6(lean_object* v_toPure_236_, lean_object* v_text_237_, lean_object* v_logMessage_238_, lean_object* v_toBind_239_, lean_object* v_getFileName_240_, lean_object* v_inst_241_, lean_object* v___f_242_, lean_object* v_ictx_243_, lean_object* v_source_244_, lean_object* v___f_245_, lean_object* v_env_246_, lean_object* v_____do__lift_247_, lean_object* v_____do__lift_248_, lean_object* v_val_249_, lean_object* v___y_250_, lean_object* v___x_251_, lean_object* v_____do__lift_252_){
_start:
{
lean_object* v___y_254_; lean_object* v_pmctx_276_; lean_object* v_blockCtxt_277_; lean_object* v___x_278_; lean_object* v_s_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_s_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
lean_inc_ref(v_env_246_);
v_pmctx_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_276_, 0, v_env_246_);
lean_ctor_set(v_pmctx_276_, 1, v_____do__lift_247_);
lean_ctor_set(v_pmctx_276_, 2, v_____do__lift_248_);
lean_ctor_set(v_pmctx_276_, 3, v_____do__lift_252_);
lean_inc(v_val_249_);
lean_inc_ref(v_text_237_);
v_blockCtxt_277_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_237_, v_val_249_, v___y_250_);
v___x_278_ = l_Lean_Parser_mkParserState(v_source_244_);
lean_inc_ref(v___x_278_);
v_s_279_ = l_Lean_Parser_ParserState_setPos(v___x_278_, v_val_249_);
v___x_280_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_280_, 0, v_blockCtxt_277_);
v___x_281_ = l_Lean_Parser_getTokenTable(v_env_246_);
lean_inc_ref(v___x_281_);
lean_inc_ref(v_pmctx_276_);
lean_inc_ref(v_ictx_243_);
v_s_282_ = l_Lean_Parser_ParserFn_run(v___x_280_, v_ictx_243_, v_pmctx_276_, v___x_281_, v_s_279_);
lean_inc_ref(v_s_282_);
v___x_283_ = l_Lean_Parser_ParserState_allErrors(v_s_282_);
v___x_284_ = lean_array_get_size(v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec_ref(v___x_281_);
lean_dec_ref(v___x_278_);
lean_dec_ref_known(v_pmctx_276_, 4);
lean_dec(v___x_251_);
v___y_254_ = v_s_282_;
goto v___jp_253_;
}
else
{
lean_object* v_pos_287_; uint8_t v___x_288_; 
v_pos_287_ = lean_ctor_get(v_s_282_, 2);
lean_inc(v_pos_287_);
v___x_288_ = l_Lean_Parser_InputContext_atEnd(v_ictx_243_, v_pos_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v_s_282_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_251_);
lean_ctor_set(v___x_291_, 1, v___x_285_);
v___x_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_292_, 0, v___x_285_);
lean_ctor_set(v___x_292_, 1, v___x_289_);
lean_ctor_set(v___x_292_, 2, v___x_290_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
lean_ctor_set(v___x_292_, 4, v___x_285_);
v___x_293_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_293_, 0, v___x_292_);
v___x_294_ = l_Lean_Parser_ParserState_setPos(v___x_278_, v_pos_287_);
lean_inc_ref(v_ictx_243_);
v___x_295_ = l_Lean_Parser_ParserFn_run(v___x_293_, v_ictx_243_, v_pmctx_276_, v___x_281_, v___x_294_);
v___y_254_ = v___x_295_;
goto v___jp_253_;
}
else
{
lean_dec(v_pos_287_);
lean_dec_ref(v___x_281_);
lean_dec_ref(v___x_278_);
lean_dec_ref_known(v_pmctx_276_, 4);
lean_dec(v___x_251_);
v___y_254_ = v_s_282_;
goto v___jp_253_;
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
lean_inc_ref(v___y_254_);
v___x_255_ = l_Lean_Parser_ParserState_allErrors(v___y_254_);
v___x_256_ = lean_array_get_size(v___x_255_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_nat_dec_eq(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___f_262_; size_t v_sz_263_; size_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___y_254_);
lean_dec(v___f_245_);
lean_dec_ref(v_source_244_);
lean_dec_ref(v_ictx_243_);
v___x_259_ = lean_box(0);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_260_, 0, v___x_259_);
lean_closure_set(v___f_260_, 1, v_toPure_236_);
v___x_261_ = lean_box(v___x_258_);
lean_inc(v_toBind_239_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__4___boxed), 9, 6);
lean_closure_set(v___f_262_, 0, v_text_237_);
lean_closure_set(v___f_262_, 1, v___x_261_);
lean_closure_set(v___f_262_, 2, v_logMessage_238_);
lean_closure_set(v___f_262_, 3, v_toBind_239_);
lean_closure_set(v___f_262_, 4, v___f_260_);
lean_closure_set(v___f_262_, 5, v_getFileName_240_);
v_sz_263_ = lean_array_size(v___x_255_);
v___x_264_ = ((size_t)0ULL);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_241_, v___x_255_, v___f_262_, v_sz_263_, v___x_264_, v___x_259_);
v___x_266_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_265_, v___f_242_);
return v___x_266_;
}
else
{
lean_object* v_stxStack_267_; lean_object* v_pos_268_; uint8_t v___x_269_; 
lean_dec_ref(v___x_255_);
lean_dec(v___f_242_);
lean_dec_ref(v_inst_241_);
v_stxStack_267_ = lean_ctor_get(v___y_254_, 0);
lean_inc_ref(v_stxStack_267_);
v_pos_268_ = lean_ctor_get(v___y_254_, 2);
lean_inc(v_pos_268_);
lean_dec_ref(v___y_254_);
v___x_269_ = l_Lean_Parser_InputContext_atEnd(v_ictx_243_, v_pos_268_);
lean_dec_ref(v_ictx_243_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___f_271_; lean_object* v___x_272_; 
lean_dec_ref(v_stxStack_267_);
lean_dec(v_toPure_236_);
v___x_270_ = lean_box(v___x_269_);
lean_inc(v_toBind_239_);
v___f_271_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_271_, 0, v_text_237_);
lean_closure_set(v___f_271_, 1, v_pos_268_);
lean_closure_set(v___f_271_, 2, v_source_244_);
lean_closure_set(v___f_271_, 3, v___x_270_);
lean_closure_set(v___f_271_, 4, v_logMessage_238_);
lean_closure_set(v___f_271_, 5, v_toBind_239_);
lean_closure_set(v___f_271_, 6, v___f_245_);
v___x_272_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v_getFileName_240_, v___f_271_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_pos_268_);
lean_dec(v___f_245_);
lean_dec_ref(v_source_244_);
lean_dec(v_getFileName_240_);
lean_dec(v_toBind_239_);
lean_dec(v_logMessage_238_);
lean_dec_ref(v_text_237_);
v___x_273_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_267_);
lean_dec_ref(v_stxStack_267_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_apply_2(v_toPure_236_, lean_box(0), v___x_274_);
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_toPure_296_ = _args[0];
lean_object* v_text_297_ = _args[1];
lean_object* v_logMessage_298_ = _args[2];
lean_object* v_toBind_299_ = _args[3];
lean_object* v_getFileName_300_ = _args[4];
lean_object* v_inst_301_ = _args[5];
lean_object* v___f_302_ = _args[6];
lean_object* v_ictx_303_ = _args[7];
lean_object* v_source_304_ = _args[8];
lean_object* v___f_305_ = _args[9];
lean_object* v_env_306_ = _args[10];
lean_object* v_____do__lift_307_ = _args[11];
lean_object* v_____do__lift_308_ = _args[12];
lean_object* v_val_309_ = _args[13];
lean_object* v___y_310_ = _args[14];
lean_object* v___x_311_ = _args[15];
lean_object* v_____do__lift_312_ = _args[16];
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_parseVersoDocString___redArg___lam__6(v_toPure_296_, v_text_297_, v_logMessage_298_, v_toBind_299_, v_getFileName_300_, v_inst_301_, v___f_302_, v_ictx_303_, v_source_304_, v___f_305_, v_env_306_, v_____do__lift_307_, v_____do__lift_308_, v_val_309_, v___y_310_, v___x_311_, v_____do__lift_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7(lean_object* v_toPure_314_, lean_object* v_text_315_, lean_object* v_logMessage_316_, lean_object* v_toBind_317_, lean_object* v_getFileName_318_, lean_object* v_inst_319_, lean_object* v___f_320_, lean_object* v_ictx_321_, lean_object* v_source_322_, lean_object* v___f_323_, lean_object* v_env_324_, lean_object* v_____do__lift_325_, lean_object* v_val_326_, lean_object* v___y_327_, lean_object* v___x_328_, lean_object* v_getOpenDecls_329_, lean_object* v_____do__lift_330_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; 
lean_inc(v_toBind_317_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_331_, 0, v_toPure_314_);
lean_closure_set(v___f_331_, 1, v_text_315_);
lean_closure_set(v___f_331_, 2, v_logMessage_316_);
lean_closure_set(v___f_331_, 3, v_toBind_317_);
lean_closure_set(v___f_331_, 4, v_getFileName_318_);
lean_closure_set(v___f_331_, 5, v_inst_319_);
lean_closure_set(v___f_331_, 6, v___f_320_);
lean_closure_set(v___f_331_, 7, v_ictx_321_);
lean_closure_set(v___f_331_, 8, v_source_322_);
lean_closure_set(v___f_331_, 9, v___f_323_);
lean_closure_set(v___f_331_, 10, v_env_324_);
lean_closure_set(v___f_331_, 11, v_____do__lift_325_);
lean_closure_set(v___f_331_, 12, v_____do__lift_330_);
lean_closure_set(v___f_331_, 13, v_val_326_);
lean_closure_set(v___f_331_, 14, v___y_327_);
lean_closure_set(v___f_331_, 15, v___x_328_);
v___x_332_ = lean_apply_4(v_toBind_317_, lean_box(0), lean_box(0), v_getOpenDecls_329_, v___f_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_toPure_333_ = _args[0];
lean_object* v_text_334_ = _args[1];
lean_object* v_logMessage_335_ = _args[2];
lean_object* v_toBind_336_ = _args[3];
lean_object* v_getFileName_337_ = _args[4];
lean_object* v_inst_338_ = _args[5];
lean_object* v___f_339_ = _args[6];
lean_object* v_ictx_340_ = _args[7];
lean_object* v_source_341_ = _args[8];
lean_object* v___f_342_ = _args[9];
lean_object* v_env_343_ = _args[10];
lean_object* v_____do__lift_344_ = _args[11];
lean_object* v_val_345_ = _args[12];
lean_object* v___y_346_ = _args[13];
lean_object* v___x_347_ = _args[14];
lean_object* v_getOpenDecls_348_ = _args[15];
lean_object* v_____do__lift_349_ = _args[16];
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_parseVersoDocString___redArg___lam__7(v_toPure_333_, v_text_334_, v_logMessage_335_, v_toBind_336_, v_getFileName_337_, v_inst_338_, v___f_339_, v_ictx_340_, v_source_341_, v___f_342_, v_env_343_, v_____do__lift_344_, v_val_345_, v___y_346_, v___x_347_, v_getOpenDecls_348_, v_____do__lift_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__8(lean_object* v_inst_351_, lean_object* v_toPure_352_, lean_object* v_text_353_, lean_object* v_logMessage_354_, lean_object* v_toBind_355_, lean_object* v_getFileName_356_, lean_object* v_inst_357_, lean_object* v___f_358_, lean_object* v_ictx_359_, lean_object* v_source_360_, lean_object* v___f_361_, lean_object* v_env_362_, lean_object* v_val_363_, lean_object* v___y_364_, lean_object* v___x_365_, lean_object* v_____do__lift_366_){
_start:
{
lean_object* v_getCurrNamespace_367_; lean_object* v_getOpenDecls_368_; lean_object* v___f_369_; lean_object* v___x_370_; 
v_getCurrNamespace_367_ = lean_ctor_get(v_inst_351_, 0);
lean_inc(v_getCurrNamespace_367_);
v_getOpenDecls_368_ = lean_ctor_get(v_inst_351_, 1);
lean_inc(v_getOpenDecls_368_);
lean_dec_ref(v_inst_351_);
lean_inc(v_toBind_355_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_369_, 0, v_toPure_352_);
lean_closure_set(v___f_369_, 1, v_text_353_);
lean_closure_set(v___f_369_, 2, v_logMessage_354_);
lean_closure_set(v___f_369_, 3, v_toBind_355_);
lean_closure_set(v___f_369_, 4, v_getFileName_356_);
lean_closure_set(v___f_369_, 5, v_inst_357_);
lean_closure_set(v___f_369_, 6, v___f_358_);
lean_closure_set(v___f_369_, 7, v_ictx_359_);
lean_closure_set(v___f_369_, 8, v_source_360_);
lean_closure_set(v___f_369_, 9, v___f_361_);
lean_closure_set(v___f_369_, 10, v_env_362_);
lean_closure_set(v___f_369_, 11, v_____do__lift_366_);
lean_closure_set(v___f_369_, 12, v_val_363_);
lean_closure_set(v___f_369_, 13, v___y_364_);
lean_closure_set(v___f_369_, 14, v___x_365_);
lean_closure_set(v___f_369_, 15, v_getOpenDecls_368_);
v___x_370_ = lean_apply_4(v_toBind_355_, lean_box(0), lean_box(0), v_getCurrNamespace_367_, v___f_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__9(lean_object* v_source_371_, lean_object* v_text_372_, lean_object* v___y_373_, lean_object* v_inst_374_, lean_object* v_toPure_375_, lean_object* v_logMessage_376_, lean_object* v_toBind_377_, lean_object* v_getFileName_378_, lean_object* v_inst_379_, lean_object* v___f_380_, lean_object* v___f_381_, lean_object* v_env_382_, lean_object* v_val_383_, lean_object* v___x_384_, lean_object* v_inst_385_, lean_object* v_____do__lift_386_){
_start:
{
lean_object* v_ictx_387_; lean_object* v___f_388_; lean_object* v___x_389_; 
lean_inc(v___y_373_);
lean_inc_ref(v_text_372_);
lean_inc_ref(v_source_371_);
v_ictx_387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_387_, 0, v_source_371_);
lean_ctor_set(v_ictx_387_, 1, v_____do__lift_386_);
lean_ctor_set(v_ictx_387_, 2, v_text_372_);
lean_ctor_set(v_ictx_387_, 3, v___y_373_);
lean_inc(v_toBind_377_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__8), 16, 15);
lean_closure_set(v___f_388_, 0, v_inst_374_);
lean_closure_set(v___f_388_, 1, v_toPure_375_);
lean_closure_set(v___f_388_, 2, v_text_372_);
lean_closure_set(v___f_388_, 3, v_logMessage_376_);
lean_closure_set(v___f_388_, 4, v_toBind_377_);
lean_closure_set(v___f_388_, 5, v_getFileName_378_);
lean_closure_set(v___f_388_, 6, v_inst_379_);
lean_closure_set(v___f_388_, 7, v___f_380_);
lean_closure_set(v___f_388_, 8, v_ictx_387_);
lean_closure_set(v___f_388_, 9, v_source_371_);
lean_closure_set(v___f_388_, 10, v___f_381_);
lean_closure_set(v___f_388_, 11, v_env_382_);
lean_closure_set(v___f_388_, 12, v_val_383_);
lean_closure_set(v___f_388_, 13, v___y_373_);
lean_closure_set(v___f_388_, 14, v___x_384_);
v___x_389_ = lean_apply_4(v_toBind_377_, lean_box(0), lean_box(0), v_inst_385_, v___f_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__10(lean_object* v_inst_390_, lean_object* v_source_391_, lean_object* v_text_392_, lean_object* v___y_393_, lean_object* v_inst_394_, lean_object* v_toPure_395_, lean_object* v_toBind_396_, lean_object* v_inst_397_, lean_object* v___f_398_, lean_object* v___f_399_, lean_object* v_val_400_, lean_object* v___x_401_, lean_object* v_inst_402_, lean_object* v_env_403_){
_start:
{
lean_object* v_getFileName_404_; lean_object* v_logMessage_405_; lean_object* v___f_406_; lean_object* v___x_407_; 
v_getFileName_404_ = lean_ctor_get(v_inst_390_, 2);
lean_inc_n(v_getFileName_404_, 2);
v_logMessage_405_ = lean_ctor_get(v_inst_390_, 4);
lean_inc(v_logMessage_405_);
lean_dec_ref(v_inst_390_);
lean_inc(v_toBind_396_);
v___f_406_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__9), 16, 15);
lean_closure_set(v___f_406_, 0, v_source_391_);
lean_closure_set(v___f_406_, 1, v_text_392_);
lean_closure_set(v___f_406_, 2, v___y_393_);
lean_closure_set(v___f_406_, 3, v_inst_394_);
lean_closure_set(v___f_406_, 4, v_toPure_395_);
lean_closure_set(v___f_406_, 5, v_logMessage_405_);
lean_closure_set(v___f_406_, 6, v_toBind_396_);
lean_closure_set(v___f_406_, 7, v_getFileName_404_);
lean_closure_set(v___f_406_, 8, v_inst_397_);
lean_closure_set(v___f_406_, 9, v___f_398_);
lean_closure_set(v___f_406_, 10, v___f_399_);
lean_closure_set(v___f_406_, 11, v_env_403_);
lean_closure_set(v___f_406_, 12, v_val_400_);
lean_closure_set(v___f_406_, 13, v___x_401_);
lean_closure_set(v___f_406_, 14, v_inst_402_);
v___x_407_ = lean_apply_4(v_toBind_396_, lean_box(0), lean_box(0), v_getFileName_404_, v___f_406_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__11___closed__0));
v___x_410_ = l_Lean_stringToMessageData(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg___lam__11(lean_object* v_docComment_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_toPure_415_, lean_object* v_toBind_416_, lean_object* v_inst_417_, lean_object* v___f_418_, lean_object* v___f_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_text_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_unsigned_to_nat(1u);
v___x_424_ = l_Lean_Syntax_getArg(v_docComment_411_, v___x_423_);
v___x_425_ = 1;
v___x_426_ = l_Lean_Syntax_getPos_x3f(v___x_424_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 1)
{
lean_object* v_val_427_; lean_object* v___x_428_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = l_Lean_Syntax_getTailPos_x3f(v___x_424_, v___x_425_);
lean_dec(v___x_424_);
if (lean_obj_tag(v___x_428_) == 1)
{
lean_object* v_val_429_; lean_object* v_source_430_; lean_object* v___y_432_; lean_object* v___x_436_; lean_object* v_endPos_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
lean_dec_ref(v_inst_421_);
lean_dec(v_docComment_411_);
v_val_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_val_429_);
lean_dec_ref_known(v___x_428_, 1);
v_source_430_ = lean_ctor_get(v_text_422_, 0);
lean_inc_ref(v_source_430_);
v___x_436_ = lean_string_utf8_prev(v_source_430_, v_val_429_);
lean_dec(v_val_429_);
v_endPos_437_ = lean_string_utf8_prev(v_source_430_, v___x_436_);
lean_dec(v___x_436_);
v___x_438_ = lean_string_utf8_byte_size(v_source_430_);
v___x_439_ = lean_nat_dec_le(v_endPos_437_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec(v_endPos_437_);
v___y_432_ = v___x_438_;
goto v___jp_431_;
}
else
{
v___y_432_ = v_endPos_437_;
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v_getEnv_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_getEnv_433_ = lean_ctor_get(v_inst_412_, 0);
lean_inc(v_getEnv_433_);
lean_dec_ref(v_inst_412_);
lean_inc(v_toBind_416_);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__10), 14, 13);
lean_closure_set(v___f_434_, 0, v_inst_413_);
lean_closure_set(v___f_434_, 1, v_source_430_);
lean_closure_set(v___f_434_, 2, v_text_422_);
lean_closure_set(v___f_434_, 3, v___y_432_);
lean_closure_set(v___f_434_, 4, v_inst_414_);
lean_closure_set(v___f_434_, 5, v_toPure_415_);
lean_closure_set(v___f_434_, 6, v_toBind_416_);
lean_closure_set(v___f_434_, 7, v_inst_417_);
lean_closure_set(v___f_434_, 8, v___f_418_);
lean_closure_set(v___f_434_, 9, v___f_419_);
lean_closure_set(v___f_434_, 10, v_val_427_);
lean_closure_set(v___f_434_, 11, v___x_423_);
lean_closure_set(v___f_434_, 12, v_inst_420_);
v___x_435_ = lean_apply_4(v_toBind_416_, lean_box(0), lean_box(0), v_getEnv_433_, v___f_434_);
return v___x_435_;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v___x_428_);
lean_dec(v_val_427_);
lean_dec_ref(v_text_422_);
lean_dec(v_inst_420_);
lean_dec(v___f_419_);
lean_dec(v___f_418_);
lean_dec(v_toBind_416_);
lean_dec(v_toPure_415_);
lean_dec_ref(v_inst_414_);
lean_dec_ref(v_inst_413_);
lean_dec_ref(v_inst_412_);
v___x_440_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_441_ = l_Lean_throwErrorAt___redArg(v_inst_417_, v_inst_421_, v_docComment_411_, v___x_440_);
return v___x_441_;
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___x_426_);
lean_dec(v___x_424_);
lean_dec_ref(v_text_422_);
lean_dec(v_inst_420_);
lean_dec(v___f_419_);
lean_dec(v___f_418_);
lean_dec(v_toBind_416_);
lean_dec(v_toPure_415_);
lean_dec_ref(v_inst_414_);
lean_dec_ref(v_inst_413_);
lean_dec_ref(v_inst_412_);
v___x_442_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_443_ = l_Lean_throwErrorAt___redArg(v_inst_417_, v_inst_421_, v_docComment_411_, v___x_442_);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___redArg(lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_docComment_461_){
_start:
{
lean_object* v_toApplicative_462_; lean_object* v_toBind_463_; lean_object* v_toPure_464_; lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_toApplicative_462_ = lean_ctor_get(v_inst_454_, 0);
v_toBind_463_ = lean_ctor_get(v_inst_454_, 1);
lean_inc_n(v_toBind_463_, 2);
v_toPure_464_ = lean_ctor_get(v_toApplicative_462_, 1);
lean_inc_n(v_toPure_464_, 4);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__0), 2, 1);
lean_closure_set(v___f_465_, 0, v_toPure_464_);
v___f_466_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__1), 2, 1);
lean_closure_set(v___f_466_, 0, v_toPure_464_);
lean_inc_n(v_docComment_461_, 2);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__11), 12, 11);
lean_closure_set(v___f_467_, 0, v_docComment_461_);
lean_closure_set(v___f_467_, 1, v_inst_457_);
lean_closure_set(v___f_467_, 2, v_inst_459_);
lean_closure_set(v___f_467_, 3, v_inst_460_);
lean_closure_set(v___f_467_, 4, v_toPure_464_);
lean_closure_set(v___f_467_, 5, v_toBind_463_);
lean_closure_set(v___f_467_, 6, v_inst_454_);
lean_closure_set(v___f_467_, 7, v___f_466_);
lean_closure_set(v___f_467_, 8, v___f_465_);
lean_closure_set(v___f_467_, 9, v_inst_458_);
lean_closure_set(v___f_467_, 10, v_inst_456_);
v___x_468_ = l_Lean_Syntax_getKind(v_docComment_461_);
v___x_469_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_470_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_471_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_472_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_473_ = lean_name_eq(v___x_468_, v___x_472_);
lean_dec(v___x_468_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
lean_dec(v_toPure_464_);
lean_dec(v_docComment_461_);
v___x_474_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = l_Lean_Syntax_getArg(v_docComment_461_, v___x_475_);
lean_dec(v_docComment_461_);
if (lean_obj_tag(v___x_476_) == 1)
{
lean_object* v_kind_477_; 
v_kind_477_ = lean_ctor_get(v___x_476_, 1);
lean_inc(v_kind_477_);
if (lean_obj_tag(v_kind_477_) == 1)
{
lean_object* v_pre_478_; 
v_pre_478_ = lean_ctor_get(v_kind_477_, 0);
lean_inc(v_pre_478_);
if (lean_obj_tag(v_pre_478_) == 1)
{
lean_object* v_pre_479_; 
v_pre_479_ = lean_ctor_get(v_pre_478_, 0);
lean_inc(v_pre_479_);
if (lean_obj_tag(v_pre_479_) == 1)
{
lean_object* v_pre_480_; 
v_pre_480_ = lean_ctor_get(v_pre_479_, 0);
lean_inc(v_pre_480_);
if (lean_obj_tag(v_pre_480_) == 1)
{
lean_object* v_pre_481_; 
v_pre_481_ = lean_ctor_get(v_pre_480_, 0);
lean_inc(v_pre_481_);
if (lean_obj_tag(v_pre_481_) == 0)
{
lean_object* v_info_482_; lean_object* v_args_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_511_; 
v_info_482_ = lean_ctor_get(v___x_476_, 0);
v_args_483_ = lean_ctor_get(v___x_476_, 2);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___x_476_, 1);
lean_dec(v_unused_512_);
v___x_485_ = v___x_476_;
v_isShared_486_ = v_isSharedCheck_511_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_args_483_);
lean_inc(v_info_482_);
lean_dec(v___x_476_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_511_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v_str_487_; lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; uint8_t v___x_491_; 
v_str_487_ = lean_ctor_get(v_kind_477_, 1);
lean_inc_ref(v_str_487_);
lean_dec_ref_known(v_kind_477_, 2);
v_str_488_ = lean_ctor_get(v_pre_478_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref_known(v_pre_478_, 2);
v_str_489_ = lean_ctor_get(v_pre_479_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref_known(v_pre_479_, 2);
v_str_490_ = lean_ctor_get(v_pre_480_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref_known(v_pre_480_, 2);
v___x_491_ = lean_string_dec_eq(v_str_490_, v___x_469_);
lean_dec_ref(v_str_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_del_object(v___x_485_);
lean_dec_ref(v_args_483_);
lean_dec(v_info_482_);
lean_dec(v_toPure_464_);
v___x_492_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_string_dec_eq(v_str_489_, v___x_470_);
lean_dec_ref(v_str_489_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_del_object(v___x_485_);
lean_dec_ref(v_args_483_);
lean_dec(v_info_482_);
lean_dec(v_toPure_464_);
v___x_494_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_494_;
}
else
{
uint8_t v___x_495_; 
v___x_495_ = lean_string_dec_eq(v_str_488_, v___x_471_);
lean_dec_ref(v_str_488_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec_ref(v_str_487_);
lean_del_object(v___x_485_);
lean_dec_ref(v_args_483_);
lean_dec(v_info_482_);
lean_dec(v_toPure_464_);
v___x_496_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_498_ = lean_string_dec_eq(v_str_487_, v___x_497_);
lean_dec_ref(v_str_487_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_del_object(v___x_485_);
lean_dec_ref(v_args_483_);
lean_dec(v_info_482_);
lean_dec(v_toPure_464_);
v___x_499_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec_ref(v___f_467_);
lean_dec(v_toBind_463_);
lean_dec(v_inst_455_);
v___x_500_ = l_Lean_Name_str___override(v_pre_481_, v___x_469_);
v___x_501_ = l_Lean_Name_str___override(v___x_500_, v___x_470_);
v___x_502_ = l_Lean_Name_str___override(v___x_501_, v___x_471_);
v___x_503_ = l_Lean_Name_str___override(v___x_502_, v___x_497_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_503_);
v___x_505_ = v___x_485_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_info_482_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_args_483_);
v___x_505_ = v_reuseFailAlloc_510_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = l_Lean_Syntax_getArg(v___x_505_, v___x_506_);
lean_dec_ref(v___x_505_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_apply_2(v_toPure_464_, lean_box(0), v___x_508_);
return v___x_509_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_513_; 
lean_dec(v_pre_481_);
lean_dec_ref_known(v_pre_480_, 2);
lean_dec_ref_known(v_pre_479_, 2);
lean_dec_ref_known(v_pre_478_, 2);
lean_dec_ref_known(v_kind_477_, 2);
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v_toPure_464_);
v___x_513_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_513_;
}
}
else
{
lean_object* v___x_514_; 
lean_dec_ref_known(v_pre_479_, 2);
lean_dec(v_pre_480_);
lean_dec_ref_known(v_pre_478_, 2);
lean_dec_ref_known(v_kind_477_, 2);
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v_toPure_464_);
v___x_514_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_514_;
}
}
else
{
lean_object* v___x_515_; 
lean_dec(v_pre_479_);
lean_dec_ref_known(v_pre_478_, 2);
lean_dec_ref_known(v_kind_477_, 2);
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v_toPure_464_);
v___x_515_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_515_;
}
}
else
{
lean_object* v___x_516_; 
lean_dec_ref_known(v_kind_477_, 2);
lean_dec(v_pre_478_);
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v_toPure_464_);
v___x_516_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_516_;
}
}
else
{
lean_object* v___x_517_; 
lean_dec(v_kind_477_);
lean_dec_ref_known(v___x_476_, 3);
lean_dec(v_toPure_464_);
v___x_517_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_517_;
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v___x_476_);
lean_dec(v_toPure_464_);
v___x_518_ = lean_apply_4(v_toBind_463_, lean_box(0), lean_box(0), v_inst_455_, v___f_467_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_m_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_docComment_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_parseVersoDocString___redArg(v_inst_520_, v_inst_521_, v_inst_522_, v_inst_523_, v_inst_524_, v_inst_525_, v_inst_526_, v_docComment_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0(lean_object* v_text_529_, lean_object* v_pos_530_, lean_object* v_source_531_, uint8_t v___x_532_, lean_object* v_logMessage_533_, lean_object* v_____do__lift_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint32_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_535_ = l_Lean_FileMap_toPosition(v_text_529_, v_pos_530_);
v___x_536_ = lean_box(0);
v___x_537_ = 2;
v___x_538_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_539_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_540_ = lean_string_utf8_get(v_source_531_, v_pos_530_);
v___x_541_ = lean_string_push(v___x_538_, v___x_540_);
v___x_542_ = lean_string_append(v___x_539_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
v___x_546_ = l_Lean_MessageData_ofFormat(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_547_, 0, v_____do__lift_534_);
lean_ctor_set(v___x_547_, 1, v___x_535_);
lean_ctor_set(v___x_547_, 2, v___x_536_);
lean_ctor_set(v___x_547_, 3, v___x_538_);
lean_ctor_set(v___x_547_, 4, v___x_546_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*5, v___x_532_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*5 + 1, v___x_537_);
lean_ctor_set_uint8(v___x_547_, sizeof(void*)*5 + 2, v___x_532_);
v___x_548_ = lean_apply_1(v_logMessage_533_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__0___boxed(lean_object* v_text_549_, lean_object* v_pos_550_, lean_object* v_source_551_, lean_object* v___x_552_, lean_object* v_logMessage_553_, lean_object* v_____do__lift_554_){
_start:
{
uint8_t v___x_1166__boxed_555_; lean_object* v_res_556_; 
v___x_1166__boxed_555_ = lean_unbox(v___x_552_);
v_res_556_ = l_Lean_reportVersoParseFailure___redArg___lam__0(v_text_549_, v_pos_550_, v_source_551_, v___x_1166__boxed_555_, v_logMessage_553_, v_____do__lift_554_);
lean_dec_ref(v_source_551_);
lean_dec(v_pos_550_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1(lean_object* v_toPure_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v___y_560_, lean_object* v_ictx_561_, lean_object* v_text_562_, lean_object* v_source_563_, lean_object* v_logMessage_564_, lean_object* v_toBind_565_, lean_object* v_getFileName_566_, lean_object* v_____s_567_){
_start:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_size(v___x_558_);
v___x_572_ = lean_nat_dec_eq(v___x_571_, v___x_559_);
if (v___x_572_ == 0)
{
lean_dec(v_getFileName_566_);
lean_dec(v_toBind_565_);
lean_dec(v_logMessage_564_);
lean_dec_ref(v_source_563_);
lean_dec_ref(v_text_562_);
lean_dec_ref(v___y_560_);
goto v___jp_568_;
}
else
{
lean_object* v_pos_573_; uint8_t v___x_574_; 
v_pos_573_ = lean_ctor_get(v___y_560_, 2);
lean_inc(v_pos_573_);
lean_dec_ref(v___y_560_);
v___x_574_ = l_Lean_Parser_InputContext_atEnd(v_ictx_561_, v_pos_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___x_577_; 
lean_dec(v_toPure_557_);
v___x_575_ = lean_box(v___x_574_);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_576_, 0, v_text_562_);
lean_closure_set(v___f_576_, 1, v_pos_573_);
lean_closure_set(v___f_576_, 2, v_source_563_);
lean_closure_set(v___f_576_, 3, v___x_575_);
lean_closure_set(v___f_576_, 4, v_logMessage_564_);
v___x_577_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v_getFileName_566_, v___f_576_);
return v___x_577_;
}
else
{
lean_dec(v_pos_573_);
lean_dec(v_getFileName_566_);
lean_dec(v_toBind_565_);
lean_dec(v_logMessage_564_);
lean_dec_ref(v_source_563_);
lean_dec_ref(v_text_562_);
goto v___jp_568_;
}
}
v___jp_568_:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_box(0);
v___x_570_ = lean_apply_2(v_toPure_557_, lean_box(0), v___x_569_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__1___boxed(lean_object* v_toPure_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v___y_581_, lean_object* v_ictx_582_, lean_object* v_text_583_, lean_object* v_source_584_, lean_object* v_logMessage_585_, lean_object* v_toBind_586_, lean_object* v_getFileName_587_, lean_object* v_____s_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_reportVersoParseFailure___redArg___lam__1(v_toPure_578_, v___x_579_, v___x_580_, v___y_581_, v_ictx_582_, v_text_583_, v_source_584_, v_logMessage_585_, v_toBind_586_, v_getFileName_587_, v_____s_588_);
lean_dec_ref(v_ictx_582_);
lean_dec(v___x_580_);
lean_dec_ref(v___x_579_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3(lean_object* v_text_590_, lean_object* v_fst_591_, lean_object* v_snd_592_, lean_object* v_logMessage_593_, lean_object* v_toBind_594_, lean_object* v___f_595_, lean_object* v_____do__lift_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_597_ = l_Lean_FileMap_toPosition(v_text_590_, v_fst_591_);
v___x_598_ = lean_box(0);
v___x_599_ = 0;
v___x_600_ = 2;
v___x_601_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_602_ = l_Lean_Parser_Error_toString(v_snd_592_);
v___x_603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = l_Lean_MessageData_ofFormat(v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_605_, 0, v_____do__lift_596_);
lean_ctor_set(v___x_605_, 1, v___x_597_);
lean_ctor_set(v___x_605_, 2, v___x_598_);
lean_ctor_set(v___x_605_, 3, v___x_601_);
lean_ctor_set(v___x_605_, 4, v___x_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*5, v___x_599_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*5 + 1, v___x_600_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*5 + 2, v___x_599_);
v___x_606_ = lean_apply_1(v_logMessage_593_, v___x_605_);
v___x_607_ = lean_apply_4(v_toBind_594_, lean_box(0), lean_box(0), v___x_606_, v___f_595_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__3___boxed(lean_object* v_text_608_, lean_object* v_fst_609_, lean_object* v_snd_610_, lean_object* v_logMessage_611_, lean_object* v_toBind_612_, lean_object* v___f_613_, lean_object* v_____do__lift_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_reportVersoParseFailure___redArg___lam__3(v_text_608_, v_fst_609_, v_snd_610_, v_logMessage_611_, v_toBind_612_, v___f_613_, v_____do__lift_614_);
lean_dec(v_fst_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__2(lean_object* v_text_616_, lean_object* v_logMessage_617_, lean_object* v_toBind_618_, lean_object* v___f_619_, lean_object* v_getFileName_620_, lean_object* v_a_621_, lean_object* v_x_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_snd_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___f_627_; lean_object* v___x_628_; 
v_snd_624_ = lean_ctor_get(v_a_621_, 1);
lean_inc(v_snd_624_);
v_fst_625_ = lean_ctor_get(v_a_621_, 0);
lean_inc(v_fst_625_);
lean_dec_ref(v_a_621_);
v_snd_626_ = lean_ctor_get(v_snd_624_, 1);
lean_inc(v_snd_626_);
lean_dec(v_snd_624_);
lean_inc(v_toBind_618_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_627_, 0, v_text_616_);
lean_closure_set(v___f_627_, 1, v_fst_625_);
lean_closure_set(v___f_627_, 2, v_snd_626_);
lean_closure_set(v___f_627_, 3, v_logMessage_617_);
lean_closure_set(v___f_627_, 4, v_toBind_618_);
lean_closure_set(v___f_627_, 5, v___f_619_);
v___x_628_ = lean_apply_4(v_toBind_618_, lean_box(0), lean_box(0), v_getFileName_620_, v___f_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__4(lean_object* v_toPure_629_, lean_object* v___x_630_, lean_object* v_ictx_631_, lean_object* v_text_632_, lean_object* v_source_633_, lean_object* v_logMessage_634_, lean_object* v_toBind_635_, lean_object* v_getFileName_636_, lean_object* v_inst_637_, lean_object* v_env_638_, lean_object* v_____do__lift_639_, lean_object* v_____do__lift_640_, lean_object* v_val_641_, lean_object* v___y_642_, lean_object* v_____do__lift_643_){
_start:
{
lean_object* v___y_645_; lean_object* v_pmctx_655_; lean_object* v_blockCtxt_656_; lean_object* v___x_657_; lean_object* v_s_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_s_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
lean_inc_ref(v_env_638_);
v_pmctx_655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_655_, 0, v_env_638_);
lean_ctor_set(v_pmctx_655_, 1, v_____do__lift_639_);
lean_ctor_set(v_pmctx_655_, 2, v_____do__lift_640_);
lean_ctor_set(v_pmctx_655_, 3, v_____do__lift_643_);
lean_inc(v_val_641_);
lean_inc_ref(v_text_632_);
v_blockCtxt_656_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_text_632_, v_val_641_, v___y_642_);
v___x_657_ = l_Lean_Parser_mkParserState(v_source_633_);
lean_inc_ref(v___x_657_);
v_s_658_ = l_Lean_Parser_ParserState_setPos(v___x_657_, v_val_641_);
v___x_659_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_659_, 0, v_blockCtxt_656_);
v___x_660_ = l_Lean_Parser_getTokenTable(v_env_638_);
lean_inc_ref(v___x_660_);
lean_inc_ref(v_pmctx_655_);
lean_inc_ref(v_ictx_631_);
v_s_661_ = l_Lean_Parser_ParserFn_run(v___x_659_, v_ictx_631_, v_pmctx_655_, v___x_660_, v_s_658_);
lean_inc_ref(v_s_661_);
v___x_662_ = l_Lean_Parser_ParserState_allErrors(v_s_661_);
v___x_663_ = lean_array_get_size(v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_nat_dec_eq(v___x_663_, v___x_630_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_657_);
lean_dec_ref_known(v_pmctx_655_, 4);
v___y_645_ = v_s_661_;
goto v___jp_644_;
}
else
{
lean_object* v_pos_665_; uint8_t v___x_666_; 
v_pos_665_ = lean_ctor_get(v_s_661_, 2);
lean_inc(v_pos_665_);
v___x_666_ = l_Lean_Parser_InputContext_atEnd(v_ictx_631_, v_pos_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref(v_s_661_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_box(0);
v___x_669_ = lean_unsigned_to_nat(1u);
lean_inc_n(v___x_630_, 3);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_630_);
v___x_671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_671_, 0, v___x_630_);
lean_ctor_set(v___x_671_, 1, v___x_667_);
lean_ctor_set(v___x_671_, 2, v___x_668_);
lean_ctor_set(v___x_671_, 3, v___x_670_);
lean_ctor_set(v___x_671_, 4, v___x_630_);
v___x_672_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_672_, 0, v___x_671_);
v___x_673_ = l_Lean_Parser_ParserState_setPos(v___x_657_, v_pos_665_);
lean_inc_ref(v_ictx_631_);
v___x_674_ = l_Lean_Parser_ParserFn_run(v___x_672_, v_ictx_631_, v_pmctx_655_, v___x_660_, v___x_673_);
v___y_645_ = v___x_674_;
goto v___jp_644_;
}
else
{
lean_dec(v_pos_665_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_657_);
lean_dec_ref_known(v_pmctx_655_, 4);
v___y_645_ = v_s_661_;
goto v___jp_644_;
}
}
v___jp_644_:
{
lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___f_650_; size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref(v___y_645_);
v___x_646_ = l_Lean_Parser_ParserState_allErrors(v___y_645_);
lean_inc(v_getFileName_636_);
lean_inc_n(v_toBind_635_, 2);
lean_inc(v_logMessage_634_);
lean_inc_ref(v_text_632_);
lean_inc_ref(v___x_646_);
lean_inc(v_toPure_629_);
v___f_647_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_647_, 0, v_toPure_629_);
lean_closure_set(v___f_647_, 1, v___x_646_);
lean_closure_set(v___f_647_, 2, v___x_630_);
lean_closure_set(v___f_647_, 3, v___y_645_);
lean_closure_set(v___f_647_, 4, v_ictx_631_);
lean_closure_set(v___f_647_, 5, v_text_632_);
lean_closure_set(v___f_647_, 6, v_source_633_);
lean_closure_set(v___f_647_, 7, v_logMessage_634_);
lean_closure_set(v___f_647_, 8, v_toBind_635_);
lean_closure_set(v___f_647_, 9, v_getFileName_636_);
v___x_648_ = lean_box(0);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___redArg___lam__2), 3, 2);
lean_closure_set(v___f_649_, 0, v___x_648_);
lean_closure_set(v___f_649_, 1, v_toPure_629_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__2), 8, 5);
lean_closure_set(v___f_650_, 0, v_text_632_);
lean_closure_set(v___f_650_, 1, v_logMessage_634_);
lean_closure_set(v___f_650_, 2, v_toBind_635_);
lean_closure_set(v___f_650_, 3, v___f_649_);
lean_closure_set(v___f_650_, 4, v_getFileName_636_);
v_sz_651_ = lean_array_size(v___x_646_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_637_, v___x_646_, v___f_650_, v_sz_651_, v___x_652_, v___x_648_);
v___x_654_ = lean_apply_4(v_toBind_635_, lean_box(0), lean_box(0), v___x_653_, v___f_647_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__5(lean_object* v_toPure_675_, lean_object* v___x_676_, lean_object* v_ictx_677_, lean_object* v_text_678_, lean_object* v_source_679_, lean_object* v_logMessage_680_, lean_object* v_toBind_681_, lean_object* v_getFileName_682_, lean_object* v_inst_683_, lean_object* v_env_684_, lean_object* v_____do__lift_685_, lean_object* v_val_686_, lean_object* v___y_687_, lean_object* v_getOpenDecls_688_, lean_object* v_____do__lift_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___x_691_; 
lean_inc(v_toBind_681_);
v___f_690_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__4), 15, 14);
lean_closure_set(v___f_690_, 0, v_toPure_675_);
lean_closure_set(v___f_690_, 1, v___x_676_);
lean_closure_set(v___f_690_, 2, v_ictx_677_);
lean_closure_set(v___f_690_, 3, v_text_678_);
lean_closure_set(v___f_690_, 4, v_source_679_);
lean_closure_set(v___f_690_, 5, v_logMessage_680_);
lean_closure_set(v___f_690_, 6, v_toBind_681_);
lean_closure_set(v___f_690_, 7, v_getFileName_682_);
lean_closure_set(v___f_690_, 8, v_inst_683_);
lean_closure_set(v___f_690_, 9, v_env_684_);
lean_closure_set(v___f_690_, 10, v_____do__lift_685_);
lean_closure_set(v___f_690_, 11, v_____do__lift_689_);
lean_closure_set(v___f_690_, 12, v_val_686_);
lean_closure_set(v___f_690_, 13, v___y_687_);
v___x_691_ = lean_apply_4(v_toBind_681_, lean_box(0), lean_box(0), v_getOpenDecls_688_, v___f_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__6(lean_object* v_inst_692_, lean_object* v_toPure_693_, lean_object* v___x_694_, lean_object* v_ictx_695_, lean_object* v_text_696_, lean_object* v_source_697_, lean_object* v_logMessage_698_, lean_object* v_toBind_699_, lean_object* v_getFileName_700_, lean_object* v_inst_701_, lean_object* v_env_702_, lean_object* v_val_703_, lean_object* v___y_704_, lean_object* v_____do__lift_705_){
_start:
{
lean_object* v_getCurrNamespace_706_; lean_object* v_getOpenDecls_707_; lean_object* v___f_708_; lean_object* v___x_709_; 
v_getCurrNamespace_706_ = lean_ctor_get(v_inst_692_, 0);
lean_inc(v_getCurrNamespace_706_);
v_getOpenDecls_707_ = lean_ctor_get(v_inst_692_, 1);
lean_inc(v_getOpenDecls_707_);
lean_dec_ref(v_inst_692_);
lean_inc(v_toBind_699_);
v___f_708_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__5), 15, 14);
lean_closure_set(v___f_708_, 0, v_toPure_693_);
lean_closure_set(v___f_708_, 1, v___x_694_);
lean_closure_set(v___f_708_, 2, v_ictx_695_);
lean_closure_set(v___f_708_, 3, v_text_696_);
lean_closure_set(v___f_708_, 4, v_source_697_);
lean_closure_set(v___f_708_, 5, v_logMessage_698_);
lean_closure_set(v___f_708_, 6, v_toBind_699_);
lean_closure_set(v___f_708_, 7, v_getFileName_700_);
lean_closure_set(v___f_708_, 8, v_inst_701_);
lean_closure_set(v___f_708_, 9, v_env_702_);
lean_closure_set(v___f_708_, 10, v_____do__lift_705_);
lean_closure_set(v___f_708_, 11, v_val_703_);
lean_closure_set(v___f_708_, 12, v___y_704_);
lean_closure_set(v___f_708_, 13, v_getOpenDecls_707_);
v___x_709_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v_getCurrNamespace_706_, v___f_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__7(lean_object* v_source_710_, lean_object* v_text_711_, lean_object* v___y_712_, lean_object* v_inst_713_, lean_object* v_toPure_714_, lean_object* v___x_715_, lean_object* v_logMessage_716_, lean_object* v_toBind_717_, lean_object* v_getFileName_718_, lean_object* v_inst_719_, lean_object* v_env_720_, lean_object* v_val_721_, lean_object* v_inst_722_, lean_object* v_____do__lift_723_){
_start:
{
lean_object* v_ictx_724_; lean_object* v___f_725_; lean_object* v___x_726_; 
lean_inc(v___y_712_);
lean_inc_ref(v_text_711_);
lean_inc_ref(v_source_710_);
v_ictx_724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_724_, 0, v_source_710_);
lean_ctor_set(v_ictx_724_, 1, v_____do__lift_723_);
lean_ctor_set(v_ictx_724_, 2, v_text_711_);
lean_ctor_set(v_ictx_724_, 3, v___y_712_);
lean_inc(v_toBind_717_);
v___f_725_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__6), 14, 13);
lean_closure_set(v___f_725_, 0, v_inst_713_);
lean_closure_set(v___f_725_, 1, v_toPure_714_);
lean_closure_set(v___f_725_, 2, v___x_715_);
lean_closure_set(v___f_725_, 3, v_ictx_724_);
lean_closure_set(v___f_725_, 4, v_text_711_);
lean_closure_set(v___f_725_, 5, v_source_710_);
lean_closure_set(v___f_725_, 6, v_logMessage_716_);
lean_closure_set(v___f_725_, 7, v_toBind_717_);
lean_closure_set(v___f_725_, 8, v_getFileName_718_);
lean_closure_set(v___f_725_, 9, v_inst_719_);
lean_closure_set(v___f_725_, 10, v_env_720_);
lean_closure_set(v___f_725_, 11, v_val_721_);
lean_closure_set(v___f_725_, 12, v___y_712_);
v___x_726_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v_inst_722_, v___f_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__8(lean_object* v_inst_727_, lean_object* v_source_728_, lean_object* v_text_729_, lean_object* v___y_730_, lean_object* v_inst_731_, lean_object* v_toPure_732_, lean_object* v___x_733_, lean_object* v_toBind_734_, lean_object* v_inst_735_, lean_object* v_val_736_, lean_object* v_inst_737_, lean_object* v_env_738_){
_start:
{
lean_object* v_getFileName_739_; lean_object* v_logMessage_740_; lean_object* v___f_741_; lean_object* v___x_742_; 
v_getFileName_739_ = lean_ctor_get(v_inst_727_, 2);
lean_inc_n(v_getFileName_739_, 2);
v_logMessage_740_ = lean_ctor_get(v_inst_727_, 4);
lean_inc(v_logMessage_740_);
lean_dec_ref(v_inst_727_);
lean_inc(v_toBind_734_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__7), 14, 13);
lean_closure_set(v___f_741_, 0, v_source_728_);
lean_closure_set(v___f_741_, 1, v_text_729_);
lean_closure_set(v___f_741_, 2, v___y_730_);
lean_closure_set(v___f_741_, 3, v_inst_731_);
lean_closure_set(v___f_741_, 4, v_toPure_732_);
lean_closure_set(v___f_741_, 5, v___x_733_);
lean_closure_set(v___f_741_, 6, v_logMessage_740_);
lean_closure_set(v___f_741_, 7, v_toBind_734_);
lean_closure_set(v___f_741_, 8, v_getFileName_739_);
lean_closure_set(v___f_741_, 9, v_inst_735_);
lean_closure_set(v___f_741_, 10, v_env_738_);
lean_closure_set(v___f_741_, 11, v_val_736_);
lean_closure_set(v___f_741_, 12, v_inst_737_);
v___x_742_ = lean_apply_4(v_toBind_734_, lean_box(0), lean_box(0), v_getFileName_739_, v___f_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___lam__9(lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_toPure_746_, lean_object* v___x_747_, lean_object* v_toBind_748_, lean_object* v_inst_749_, lean_object* v_val_750_, lean_object* v_inst_751_, lean_object* v_val_752_, lean_object* v_text_753_){
_start:
{
lean_object* v_source_754_; lean_object* v___y_756_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_source_754_ = lean_ctor_get(v_text_753_, 0);
lean_inc_ref(v_source_754_);
v___x_760_ = lean_string_utf8_byte_size(v_source_754_);
v___x_761_ = lean_nat_dec_le(v_val_752_, v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v_val_752_);
v___y_756_ = v___x_760_;
goto v___jp_755_;
}
else
{
v___y_756_ = v_val_752_;
goto v___jp_755_;
}
v___jp_755_:
{
lean_object* v_getEnv_757_; lean_object* v___f_758_; lean_object* v___x_759_; 
v_getEnv_757_ = lean_ctor_get(v_inst_743_, 0);
lean_inc(v_getEnv_757_);
lean_dec_ref(v_inst_743_);
lean_inc(v_toBind_748_);
v___f_758_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__8), 12, 11);
lean_closure_set(v___f_758_, 0, v_inst_744_);
lean_closure_set(v___f_758_, 1, v_source_754_);
lean_closure_set(v___f_758_, 2, v_text_753_);
lean_closure_set(v___f_758_, 3, v___y_756_);
lean_closure_set(v___f_758_, 4, v_inst_745_);
lean_closure_set(v___f_758_, 5, v_toPure_746_);
lean_closure_set(v___f_758_, 6, v___x_747_);
lean_closure_set(v___f_758_, 7, v_toBind_748_);
lean_closure_set(v___f_758_, 8, v_inst_749_);
lean_closure_set(v___f_758_, 9, v_val_750_);
lean_closure_set(v___f_758_, 10, v_inst_751_);
v___x_759_ = lean_apply_4(v_toBind_748_, lean_box(0), lean_box(0), v_getEnv_757_, v___f_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg(lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_parseFailure_768_){
_start:
{
lean_object* v_toApplicative_769_; lean_object* v_toBind_770_; lean_object* v_toPure_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
v_toApplicative_769_ = lean_ctor_get(v_inst_762_, 0);
v_toBind_770_ = lean_ctor_get(v_inst_762_, 1);
lean_inc(v_toBind_770_);
v_toPure_771_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_771_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = l_Lean_Syntax_getArg(v_parseFailure_768_, v___x_772_);
v___x_774_ = 1;
v___x_775_ = l_Lean_Syntax_getPos_x3f(v___x_773_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 1)
{
lean_object* v_val_776_; lean_object* v___x_777_; 
v_val_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_Syntax_getTailPos_x3f(v___x_773_, v___x_774_);
lean_dec(v___x_773_);
if (lean_obj_tag(v___x_777_) == 1)
{
lean_object* v_val_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v_val_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___x_777_, 1);
lean_inc(v_toBind_770_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_reportVersoParseFailure___redArg___lam__9), 11, 10);
lean_closure_set(v___f_779_, 0, v_inst_764_);
lean_closure_set(v___f_779_, 1, v_inst_766_);
lean_closure_set(v___f_779_, 2, v_inst_767_);
lean_closure_set(v___f_779_, 3, v_toPure_771_);
lean_closure_set(v___f_779_, 4, v___x_772_);
lean_closure_set(v___f_779_, 5, v_toBind_770_);
lean_closure_set(v___f_779_, 6, v_inst_762_);
lean_closure_set(v___f_779_, 7, v_val_776_);
lean_closure_set(v___f_779_, 8, v_inst_765_);
lean_closure_set(v___f_779_, 9, v_val_778_);
v___x_780_ = lean_apply_4(v_toBind_770_, lean_box(0), lean_box(0), v_inst_763_, v___f_779_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v___x_777_);
lean_dec(v_val_776_);
lean_dec(v_toBind_770_);
lean_dec_ref(v_inst_767_);
lean_dec_ref(v_inst_766_);
lean_dec(v_inst_765_);
lean_dec_ref(v_inst_764_);
lean_dec(v_inst_763_);
lean_dec_ref(v_inst_762_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_apply_2(v_toPure_771_, lean_box(0), v___x_781_);
return v___x_782_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v___x_775_);
lean_dec(v___x_773_);
lean_dec(v_toBind_770_);
lean_dec_ref(v_inst_767_);
lean_dec_ref(v_inst_766_);
lean_dec(v_inst_765_);
lean_dec_ref(v_inst_764_);
lean_dec(v_inst_763_);
lean_dec_ref(v_inst_762_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_apply_2(v_toPure_771_, lean_box(0), v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___redArg___boxed(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_parseFailure_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_reportVersoParseFailure___redArg(v_inst_785_, v_inst_786_, v_inst_787_, v_inst_788_, v_inst_789_, v_inst_790_, v_parseFailure_791_);
lean_dec(v_parseFailure_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_m_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_parseFailure_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_reportVersoParseFailure___redArg(v_inst_794_, v_inst_795_, v_inst_797_, v_inst_798_, v_inst_799_, v_inst_800_, v_parseFailure_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_m_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_parseFailure_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_reportVersoParseFailure(v_m_803_, v_inst_804_, v_inst_805_, v_inst_806_, v_inst_807_, v_inst_808_, v_inst_809_, v_inst_810_, v_parseFailure_811_);
lean_dec(v_parseFailure_811_);
lean_dec_ref(v_inst_806_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_813_, lean_object* v_declName_814_, lean_object* v_binders_815_, lean_object* v___x_816_, uint8_t v___x_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_813_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Doc_DocM_exec___redArg(v_declName_814_, v_binders_815_, v___x_816_, v___x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_825_;
}
else
{
lean_object* v_toCold_826_; lean_object* v_val_827_; lean_object* v_currRecDepth_828_; lean_object* v_ref_829_; uint8_t v_diag_830_; uint8_t v_suppressElabErrors_831_; lean_object* v_fileName_832_; lean_object* v_options_833_; lean_object* v_maxRecDepth_834_; lean_object* v_currNamespace_835_; lean_object* v_openDecls_836_; lean_object* v_initHeartbeats_837_; lean_object* v_maxHeartbeats_838_; lean_object* v_quotContext_839_; lean_object* v_currMacroScope_840_; lean_object* v_cancelTk_x3f_841_; lean_object* v_inheritedTraceOptions_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_toCold_826_ = lean_ctor_get(v___y_822_, 0);
v_val_827_ = lean_ctor_get(v_fileMap_x3f_813_, 0);
v_currRecDepth_828_ = lean_ctor_get(v___y_822_, 1);
v_ref_829_ = lean_ctor_get(v___y_822_, 2);
v_diag_830_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*3);
v_suppressElabErrors_831_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*3 + 1);
v_fileName_832_ = lean_ctor_get(v_toCold_826_, 0);
v_options_833_ = lean_ctor_get(v_toCold_826_, 2);
v_maxRecDepth_834_ = lean_ctor_get(v_toCold_826_, 3);
v_currNamespace_835_ = lean_ctor_get(v_toCold_826_, 4);
v_openDecls_836_ = lean_ctor_get(v_toCold_826_, 5);
v_initHeartbeats_837_ = lean_ctor_get(v_toCold_826_, 6);
v_maxHeartbeats_838_ = lean_ctor_get(v_toCold_826_, 7);
v_quotContext_839_ = lean_ctor_get(v_toCold_826_, 8);
v_currMacroScope_840_ = lean_ctor_get(v_toCold_826_, 9);
v_cancelTk_x3f_841_ = lean_ctor_get(v_toCold_826_, 10);
v_inheritedTraceOptions_842_ = lean_ctor_get(v_toCold_826_, 11);
lean_inc_ref(v_inheritedTraceOptions_842_);
lean_inc(v_cancelTk_x3f_841_);
lean_inc(v_currMacroScope_840_);
lean_inc(v_quotContext_839_);
lean_inc(v_maxHeartbeats_838_);
lean_inc(v_initHeartbeats_837_);
lean_inc(v_openDecls_836_);
lean_inc(v_currNamespace_835_);
lean_inc(v_maxRecDepth_834_);
lean_inc_ref(v_options_833_);
lean_inc(v_val_827_);
lean_inc_ref(v_fileName_832_);
v___x_843_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_843_, 0, v_fileName_832_);
lean_ctor_set(v___x_843_, 1, v_val_827_);
lean_ctor_set(v___x_843_, 2, v_options_833_);
lean_ctor_set(v___x_843_, 3, v_maxRecDepth_834_);
lean_ctor_set(v___x_843_, 4, v_currNamespace_835_);
lean_ctor_set(v___x_843_, 5, v_openDecls_836_);
lean_ctor_set(v___x_843_, 6, v_initHeartbeats_837_);
lean_ctor_set(v___x_843_, 7, v_maxHeartbeats_838_);
lean_ctor_set(v___x_843_, 8, v_quotContext_839_);
lean_ctor_set(v___x_843_, 9, v_currMacroScope_840_);
lean_ctor_set(v___x_843_, 10, v_cancelTk_x3f_841_);
lean_ctor_set(v___x_843_, 11, v_inheritedTraceOptions_842_);
lean_inc(v_ref_829_);
lean_inc(v_currRecDepth_828_);
v___x_844_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_currRecDepth_828_);
lean_ctor_set(v___x_844_, 2, v_ref_829_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3, v_diag_830_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*3 + 1, v_suppressElabErrors_831_);
v___x_845_ = l_Lean_Doc_DocM_exec___redArg(v_declName_814_, v_binders_815_, v___x_816_, v___x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___x_844_, v___y_823_);
lean_dec_ref_known(v___x_844_, 3);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_846_, lean_object* v_declName_847_, lean_object* v_binders_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_9725__boxed_858_; lean_object* v_res_859_; 
v___x_9725__boxed_858_ = lean_unbox(v___x_850_);
v_res_859_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_846_, v_declName_847_, v_binders_848_, v___x_849_, v___x_9725__boxed_858_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v_fileMap_x3f_846_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_860_, size_t v_i_861_, lean_object* v_bs_862_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_863_ == 0)
{
return v_bs_862_;
}
else
{
lean_object* v_v_864_; lean_object* v___x_865_; lean_object* v_bs_x27_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v_v_864_ = lean_array_uget(v_bs_862_, v_i_861_);
v___x_865_ = lean_unsigned_to_nat(0u);
v_bs_x27_866_ = lean_array_uset(v_bs_862_, v_i_861_, v___x_865_);
v___x_867_ = ((size_t)1ULL);
v___x_868_ = lean_usize_add(v_i_861_, v___x_867_);
v___x_869_ = lean_array_uset(v_bs_x27_866_, v_i_861_, v_v_864_);
v_i_861_ = v___x_868_;
v_bs_862_ = v___x_869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_871_, lean_object* v_i_872_, lean_object* v_bs_873_){
_start:
{
size_t v_sz_boxed_874_; size_t v_i_boxed_875_; lean_object* v_res_876_; 
v_sz_boxed_874_ = lean_unbox_usize(v_sz_871_);
lean_dec(v_sz_871_);
v_i_boxed_875_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_res_876_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_874_, v_i_boxed_875_, v_bs_873_);
return v_res_876_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_877_, lean_object* v_opt_878_){
_start:
{
lean_object* v_name_879_; lean_object* v_defValue_880_; lean_object* v_map_881_; lean_object* v___x_882_; 
v_name_879_ = lean_ctor_get(v_opt_878_, 0);
v_defValue_880_ = lean_ctor_get(v_opt_878_, 1);
v_map_881_ = lean_ctor_get(v_opts_877_, 0);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_881_, v_name_879_);
if (lean_obj_tag(v___x_882_) == 0)
{
uint8_t v___x_883_; 
v___x_883_ = lean_unbox(v_defValue_880_);
return v___x_883_;
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v___x_882_, 1);
if (lean_obj_tag(v_val_884_) == 1)
{
uint8_t v_v_885_; 
v_v_885_ = lean_ctor_get_uint8(v_val_884_, 0);
lean_dec_ref_known(v_val_884_, 0);
return v_v_885_;
}
else
{
uint8_t v___x_886_; 
lean_dec(v_val_884_);
v___x_886_ = lean_unbox(v_defValue_880_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_887_, lean_object* v_opt_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_887_, v_opt_888_);
lean_dec_ref(v_opt_888_);
lean_dec_ref(v_opts_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; lean_object* v_env_898_; lean_object* v___x_899_; lean_object* v_toCold_900_; lean_object* v_mctx_901_; lean_object* v_lctx_902_; lean_object* v_options_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_897_ = lean_st_ref_get(v___y_895_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_env_898_);
lean_dec(v___x_897_);
v___x_899_ = lean_st_ref_get(v___y_893_);
v_toCold_900_ = lean_ctor_get(v___y_894_, 0);
v_mctx_901_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_mctx_901_);
lean_dec(v___x_899_);
v_lctx_902_ = lean_ctor_get(v___y_892_, 2);
v_options_903_ = lean_ctor_get(v_toCold_900_, 2);
lean_inc_ref(v_options_903_);
lean_inc_ref(v_lctx_902_);
v___x_904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_904_, 0, v_env_898_);
lean_ctor_set(v___x_904_, 1, v_mctx_901_);
lean_ctor_set(v___x_904_, 2, v_lctx_902_);
lean_ctor_set(v___x_904_, 3, v_options_903_);
v___x_905_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_msgData_891_);
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
return v_res_913_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_922_, uint8_t v___y_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 1)
{
lean_object* v_pre_925_; 
v_pre_925_ = lean_ctor_get(v_x_924_, 0);
switch(lean_obj_tag(v_pre_925_))
{
case 1:
{
lean_object* v_pre_926_; 
v_pre_926_ = lean_ctor_get(v_pre_925_, 0);
switch(lean_obj_tag(v_pre_926_))
{
case 0:
{
lean_object* v_str_927_; lean_object* v_str_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_str_927_ = lean_ctor_get(v_x_924_, 1);
v_str_928_ = lean_ctor_get(v_pre_925_, 1);
v___x_929_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_930_ = lean_string_dec_eq(v_str_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_932_ = lean_string_dec_eq(v_str_928_, v___x_931_);
if (v___x_932_ == 0)
{
return v___x_932_;
}
else
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_934_ = lean_string_dec_eq(v_str_927_, v___x_933_);
if (v___x_934_ == 0)
{
return v___x_934_;
}
else
{
return v_suppressElabErrors_922_;
}
}
}
else
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_936_ = lean_string_dec_eq(v_str_927_, v___x_935_);
if (v___x_936_ == 0)
{
return v___x_936_;
}
else
{
return v_suppressElabErrors_922_;
}
}
}
case 1:
{
lean_object* v_pre_937_; 
v_pre_937_ = lean_ctor_get(v_pre_926_, 0);
if (lean_obj_tag(v_pre_937_) == 0)
{
lean_object* v_str_938_; lean_object* v_str_939_; lean_object* v_str_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_str_938_ = lean_ctor_get(v_x_924_, 1);
v_str_939_ = lean_ctor_get(v_pre_925_, 1);
v_str_940_ = lean_ctor_get(v_pre_926_, 1);
v___x_941_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_942_ = lean_string_dec_eq(v_str_940_, v___x_941_);
if (v___x_942_ == 0)
{
return v___x_942_;
}
else
{
lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_944_ = lean_string_dec_eq(v_str_939_, v___x_943_);
if (v___x_944_ == 0)
{
return v___x_944_;
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_946_ = lean_string_dec_eq(v_str_938_, v___x_945_);
if (v___x_946_ == 0)
{
return v___x_946_;
}
else
{
return v_suppressElabErrors_922_;
}
}
}
}
else
{
return v___y_923_;
}
}
default: 
{
return v___y_923_;
}
}
}
case 0:
{
lean_object* v_str_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_str_947_ = lean_ctor_get(v_x_924_, 1);
v___x_948_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_949_ = lean_string_dec_eq(v_str_947_, v___x_948_);
if (v___x_949_ == 0)
{
return v___x_949_;
}
else
{
return v_suppressElabErrors_922_;
}
}
default: 
{
return v___y_923_;
}
}
}
else
{
return v___y_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_950_, lean_object* v___y_951_, lean_object* v_x_952_){
_start:
{
uint8_t v_suppressElabErrors_boxed_953_; uint8_t v___y_9824__boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_suppressElabErrors_boxed_953_ = lean_unbox(v_suppressElabErrors_950_);
v___y_9824__boxed_954_ = lean_unbox(v___y_951_);
v_res_955_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_953_, v___y_9824__boxed_954_, v_x_952_);
lean_dec(v_x_952_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_957_, lean_object* v_msgData_958_, uint8_t v_severity_959_, uint8_t v_isSilent_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___y_967_; lean_object* v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1009_; uint8_t v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; uint8_t v___y_1034_; uint8_t v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; uint8_t v___y_1045_; uint8_t v___y_1046_; uint8_t v___x_1051_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; uint8_t v___y_1057_; uint8_t v___y_1058_; uint8_t v___y_1059_; uint8_t v___y_1061_; uint8_t v___x_1077_; 
v___x_1051_ = 2;
v___x_1077_ = l_Lean_instBEqMessageSeverity_beq(v_severity_959_, v___x_1051_);
if (v___x_1077_ == 0)
{
v___y_1061_ = v___x_1077_;
goto v___jp_1060_;
}
else
{
uint8_t v___x_1078_; 
lean_inc_ref(v_msgData_958_);
v___x_1078_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_958_);
v___y_1061_ = v___x_1078_;
goto v___jp_1060_;
}
v___jp_966_:
{
lean_object* v___x_976_; lean_object* v_toCold_977_; lean_object* v_currNamespace_978_; lean_object* v_openDecls_979_; lean_object* v_env_980_; lean_object* v_nextMacroScope_981_; lean_object* v_ngen_982_; lean_object* v_auxDeclNGen_983_; lean_object* v_traceState_984_; lean_object* v_cache_985_; lean_object* v_messages_986_; lean_object* v_infoState_987_; lean_object* v_snapshotTasks_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1002_; 
v___x_976_ = lean_st_ref_take(v___y_975_);
v_toCold_977_ = lean_ctor_get(v___y_974_, 0);
v_currNamespace_978_ = lean_ctor_get(v_toCold_977_, 4);
v_openDecls_979_ = lean_ctor_get(v_toCold_977_, 5);
v_env_980_ = lean_ctor_get(v___x_976_, 0);
v_nextMacroScope_981_ = lean_ctor_get(v___x_976_, 1);
v_ngen_982_ = lean_ctor_get(v___x_976_, 2);
v_auxDeclNGen_983_ = lean_ctor_get(v___x_976_, 3);
v_traceState_984_ = lean_ctor_get(v___x_976_, 4);
v_cache_985_ = lean_ctor_get(v___x_976_, 5);
v_messages_986_ = lean_ctor_get(v___x_976_, 6);
v_infoState_987_ = lean_ctor_get(v___x_976_, 7);
v_snapshotTasks_988_ = lean_ctor_get(v___x_976_, 8);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_990_ = v___x_976_;
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snapshotTasks_988_);
lean_inc(v_infoState_987_);
lean_inc(v_messages_986_);
lean_inc(v_cache_985_);
lean_inc(v_traceState_984_);
lean_inc(v_auxDeclNGen_983_);
lean_inc(v_ngen_982_);
lean_inc(v_nextMacroScope_981_);
lean_inc(v_env_980_);
lean_dec(v___x_976_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1002_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
lean_inc(v_openDecls_979_);
lean_inc(v_currNamespace_978_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_currNamespace_978_);
lean_ctor_set(v___x_992_, 1, v_openDecls_979_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_972_);
lean_inc_ref(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_994_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_994_, 0, v___y_967_);
lean_ctor_set(v___x_994_, 1, v___y_971_);
lean_ctor_set(v___x_994_, 2, v___y_970_);
lean_ctor_set(v___x_994_, 3, v___y_968_);
lean_ctor_set(v___x_994_, 4, v___x_993_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5, v___y_973_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 1, v___y_969_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*5 + 2, v_isSilent_960_);
v___x_995_ = l_Lean_MessageLog_add(v___x_994_, v_messages_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 6, v___x_995_);
v___x_997_ = v___x_990_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_env_980_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_nextMacroScope_981_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_ngen_982_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_auxDeclNGen_983_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_traceState_984_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_cache_985_);
lean_ctor_set(v_reuseFailAlloc_1001_, 6, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 7, v_infoState_987_);
lean_ctor_set(v_reuseFailAlloc_1001_, 8, v_snapshotTasks_988_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = lean_st_ref_put(v___y_975_, v___x_997_);
v___x_999_ = lean_box(0);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
v___jp_1003_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1027_; 
v___x_1012_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_958_);
v___x_1013_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_1012_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_inc_ref_n(v___y_1007_, 2);
v___x_1018_ = l_Lean_FileMap_toPosition(v___y_1007_, v___y_1006_);
lean_dec(v___y_1006_);
v___x_1019_ = l_Lean_FileMap_toPosition(v___y_1007_, v___y_1011_);
lean_dec(v___y_1011_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1009_ == 0)
{
lean_del_object(v___x_1016_);
lean_dec_ref(v___y_1004_);
v___y_967_ = v___y_1005_;
v___y_968_ = v___x_1021_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___x_1020_;
v___y_971_ = v___x_1018_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___y_1010_;
v___y_974_ = v___y_963_;
v___y_975_ = v___y_964_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1022_; 
lean_inc(v_a_1014_);
v___x_1022_ = l_Lean_MessageData_hasTag(v___y_1004_, v_a_1014_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec_ref_known(v___x_1020_, 1);
lean_dec_ref(v___x_1018_);
lean_dec(v_a_1014_);
v___x_1023_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1023_);
v___x_1025_ = v___x_1016_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_del_object(v___x_1016_);
v___y_967_ = v___y_1005_;
v___y_968_ = v___x_1021_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___x_1020_;
v___y_971_ = v___x_1018_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___y_1010_;
v___y_974_ = v___y_963_;
v___y_975_ = v___y_964_;
goto v___jp_966_;
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_Syntax_getTailPos_x3f(v___y_1030_, v___y_1035_);
lean_dec(v___y_1030_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_inc(v___y_1036_);
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1031_;
v___y_1006_ = v___y_1036_;
v___y_1007_ = v___y_1032_;
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1034_;
v___y_1010_ = v___y_1035_;
v___y_1011_ = v___y_1036_;
goto v___jp_1003_;
}
else
{
lean_object* v_val_1038_; 
v_val_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1031_;
v___y_1006_ = v___y_1036_;
v___y_1007_ = v___y_1032_;
v___y_1008_ = v___y_1033_;
v___y_1009_ = v___y_1034_;
v___y_1010_ = v___y_1035_;
v___y_1011_ = v_val_1038_;
goto v___jp_1003_;
}
}
v___jp_1039_:
{
lean_object* v_ref_1047_; lean_object* v___x_1048_; 
v_ref_1047_ = l_Lean_replaceRef(v_ref_957_, v___y_1042_);
v___x_1048_ = l_Lean_Syntax_getPos_x3f(v_ref_1047_, v___y_1045_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_unsigned_to_nat(0u);
v___y_1029_ = v___y_1040_;
v___y_1030_ = v_ref_1047_;
v___y_1031_ = v___y_1041_;
v___y_1032_ = v___y_1043_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1044_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v___x_1049_;
goto v___jp_1028_;
}
else
{
lean_object* v_val_1050_; 
v_val_1050_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_val_1050_);
lean_dec_ref_known(v___x_1048_, 1);
v___y_1029_ = v___y_1040_;
v___y_1030_ = v_ref_1047_;
v___y_1031_ = v___y_1041_;
v___y_1032_ = v___y_1043_;
v___y_1033_ = v___y_1046_;
v___y_1034_ = v___y_1044_;
v___y_1035_ = v___y_1045_;
v___y_1036_ = v_val_1050_;
goto v___jp_1028_;
}
}
v___jp_1052_:
{
if (v___y_1059_ == 0)
{
v___y_1040_ = v___y_1055_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1056_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1058_;
v___y_1046_ = v_severity_959_;
goto v___jp_1039_;
}
else
{
v___y_1040_ = v___y_1055_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___y_1056_;
v___y_1043_ = v___y_1054_;
v___y_1044_ = v___y_1057_;
v___y_1045_ = v___y_1058_;
v___y_1046_ = v___x_1051_;
goto v___jp_1039_;
}
}
v___jp_1060_:
{
if (v___y_1061_ == 0)
{
lean_object* v_toCold_1062_; lean_object* v_ref_1063_; uint8_t v_suppressElabErrors_1064_; lean_object* v_fileName_1065_; lean_object* v_fileMap_1066_; lean_object* v_options_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; uint8_t v___x_1071_; uint8_t v___x_1072_; 
v_toCold_1062_ = lean_ctor_get(v___y_963_, 0);
v_ref_1063_ = lean_ctor_get(v___y_963_, 2);
v_suppressElabErrors_1064_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*3 + 1);
v_fileName_1065_ = lean_ctor_get(v_toCold_1062_, 0);
v_fileMap_1066_ = lean_ctor_get(v_toCold_1062_, 1);
v_options_1067_ = lean_ctor_get(v_toCold_1062_, 2);
v___x_1068_ = lean_box(v_suppressElabErrors_1064_);
v___x_1069_ = lean_box(v___y_1061_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1070_, 0, v___x_1068_);
lean_closure_set(v___f_1070_, 1, v___x_1069_);
v___x_1071_ = 1;
v___x_1072_ = l_Lean_instBEqMessageSeverity_beq(v_severity_959_, v___x_1071_);
if (v___x_1072_ == 0)
{
v___y_1053_ = v_fileName_1065_;
v___y_1054_ = v_fileMap_1066_;
v___y_1055_ = v___f_1070_;
v___y_1056_ = v_ref_1063_;
v___y_1057_ = v_suppressElabErrors_1064_;
v___y_1058_ = v___y_1061_;
v___y_1059_ = v___x_1072_;
goto v___jp_1052_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = l_Lean_warningAsError;
v___x_1074_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1067_, v___x_1073_);
v___y_1053_ = v_fileName_1065_;
v___y_1054_ = v_fileMap_1066_;
v___y_1055_ = v___f_1070_;
v___y_1056_ = v_ref_1063_;
v___y_1057_ = v_suppressElabErrors_1064_;
v___y_1058_ = v___y_1061_;
v___y_1059_ = v___x_1074_;
goto v___jp_1052_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_msgData_958_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1079_, lean_object* v_msgData_1080_, lean_object* v_severity_1081_, lean_object* v_isSilent_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v_severity_boxed_1088_; uint8_t v_isSilent_boxed_1089_; lean_object* v_res_1090_; 
v_severity_boxed_1088_ = lean_unbox(v_severity_1081_);
v_isSilent_boxed_1089_ = lean_unbox(v_isSilent_1082_);
v_res_1090_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1079_, v_msgData_1080_, v_severity_boxed_1088_, v_isSilent_boxed_1089_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v_ref_1079_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1091_, size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v___x_1102_; 
v___x_1102_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_b_1094_);
return v___x_1103_;
}
else
{
lean_object* v_ref_1104_; lean_object* v_a_1105_; uint8_t v_severity_1106_; uint8_t v_isSilent_1107_; lean_object* v_data_1108_; lean_object* v___x_1109_; 
v_ref_1104_ = lean_ctor_get(v___y_1099_, 2);
v_a_1105_ = lean_array_uget_borrowed(v_as_1091_, v_i_1093_);
v_severity_1106_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*5 + 1);
v_isSilent_1107_ = lean_ctor_get_uint8(v_a_1105_, sizeof(void*)*5 + 2);
v_data_1108_ = lean_ctor_get(v_a_1105_, 4);
lean_inc(v_data_1108_);
v___x_1109_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1104_, v_data_1108_, v_severity_1106_, v_isSilent_1107_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; 
lean_dec_ref_known(v___x_1109_, 1);
v___x_1110_ = lean_box(0);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_add(v_i_1093_, v___x_1111_);
v_i_1093_ = v___x_1112_;
v_b_1094_ = v___x_1110_;
goto _start;
}
else
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1114_, lean_object* v_sz_1115_, lean_object* v_i_1116_, lean_object* v_b_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
size_t v_sz_boxed_1125_; size_t v_i_boxed_1126_; lean_object* v_res_1127_; 
v_sz_boxed_1125_ = lean_unbox_usize(v_sz_1115_);
lean_dec(v_sz_1115_);
v_i_boxed_1126_ = lean_unbox_usize(v_i_1116_);
lean_dec(v_i_1116_);
v_res_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1114_, v_sz_boxed_1125_, v_i_boxed_1126_, v_b_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec_ref(v_as_1114_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_infoState_1132_; lean_object* v_env_1133_; lean_object* v_nextMacroScope_1134_; lean_object* v_ngen_1135_; lean_object* v_auxDeclNGen_1136_; lean_object* v_traceState_1137_; lean_object* v_cache_1138_; lean_object* v_messages_1139_; lean_object* v_snapshotTasks_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1160_; 
v___x_1131_ = lean_st_ref_take(v___y_1129_);
v_infoState_1132_ = lean_ctor_get(v___x_1131_, 7);
v_env_1133_ = lean_ctor_get(v___x_1131_, 0);
v_nextMacroScope_1134_ = lean_ctor_get(v___x_1131_, 1);
v_ngen_1135_ = lean_ctor_get(v___x_1131_, 2);
v_auxDeclNGen_1136_ = lean_ctor_get(v___x_1131_, 3);
v_traceState_1137_ = lean_ctor_get(v___x_1131_, 4);
v_cache_1138_ = lean_ctor_get(v___x_1131_, 5);
v_messages_1139_ = lean_ctor_get(v___x_1131_, 6);
v_snapshotTasks_1140_ = lean_ctor_get(v___x_1131_, 8);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1142_ = v___x_1131_;
v_isShared_1143_ = v_isSharedCheck_1160_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snapshotTasks_1140_);
lean_inc(v_infoState_1132_);
lean_inc(v_messages_1139_);
lean_inc(v_cache_1138_);
lean_inc(v_traceState_1137_);
lean_inc(v_auxDeclNGen_1136_);
lean_inc(v_ngen_1135_);
lean_inc(v_nextMacroScope_1134_);
lean_inc(v_env_1133_);
lean_dec(v___x_1131_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1160_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_assignment_1144_; lean_object* v_lazyAssignment_1145_; lean_object* v_trees_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1159_; 
v_assignment_1144_ = lean_ctor_get(v_infoState_1132_, 0);
v_lazyAssignment_1145_ = lean_ctor_get(v_infoState_1132_, 1);
v_trees_1146_ = lean_ctor_get(v_infoState_1132_, 2);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_infoState_1132_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1148_ = v_infoState_1132_;
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_trees_1146_);
lean_inc(v_lazyAssignment_1145_);
lean_inc(v_assignment_1144_);
lean_dec(v_infoState_1132_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1159_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_assignment_1144_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_lazyAssignment_1145_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_trees_1146_);
v___x_1151_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
lean_ctor_set_uint8(v___x_1151_, sizeof(void*)*3, v_flag_1128_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 7, v___x_1151_);
v___x_1153_ = v___x_1142_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_env_1133_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_nextMacroScope_1134_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_ngen_1135_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_auxDeclNGen_1136_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_traceState_1137_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_cache_1138_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_messages_1139_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_snapshotTasks_1140_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_st_ref_put(v___y_1129_, v___x_1153_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
uint8_t v_flag_boxed_1164_; lean_object* v_res_1165_; 
v_flag_boxed_1164_ = lean_unbox(v_flag_1161_);
v_res_1165_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1164_, v___y_1162_);
lean_dec(v___y_1162_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; lean_object* v_infoState_1176_; uint8_t v_enabled_1177_; lean_object* v_a_1179_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1175_ = lean_st_ref_get(v___y_1173_);
v_infoState_1176_ = lean_ctor_get(v___x_1175_, 7);
lean_inc_ref(v_infoState_1176_);
lean_dec(v___x_1175_);
v_enabled_1177_ = lean_ctor_get_uint8(v_infoState_1176_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1176_);
v___x_1189_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1166_, v___y_1173_);
lean_dec_ref(v___x_1189_);
lean_inc(v___y_1173_);
lean_inc_ref(v___y_1172_);
lean_inc(v___y_1171_);
lean_inc_ref(v___y_1170_);
lean_inc(v___y_1169_);
lean_inc_ref(v___y_1168_);
v___x_1190_ = lean_apply_7(v_x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, lean_box(0));
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1177_, v___y_1173_);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___x_1192_, 0);
lean_dec(v_unused_1200_);
v___x_1194_ = v___x_1192_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v___x_1192_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_a_1191_);
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1191_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1201_; 
v_a_1201_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1190_, 1);
v_a_1179_ = v_a_1201_;
goto v___jp_1178_;
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v___x_1180_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1177_, v___y_1173_);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v___x_1180_, 0);
lean_dec(v_unused_1188_);
v___x_1182_ = v___x_1180_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v___x_1180_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
lean_ctor_set(v___x_1182_, 0, v_a_1179_);
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1179_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v_flag_boxed_1211_; lean_object* v_res_1212_; 
v_flag_boxed_1211_ = lean_unbox(v_flag_1202_);
v_res_1212_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1211_, v_x_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1213_, lean_object* v_binders_1214_, lean_object* v_blocks_1215_, lean_object* v_fileMap_x3f_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_a_1227_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___y_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_sz_1245_ = lean_array_size(v_blocks_1215_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1245_, v___x_1246_, v_blocks_1215_);
v___x_1248_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1248_, 0, v___x_1247_);
v___x_1249_ = 1;
v___x_1250_ = lean_box(v___x_1249_);
v___y_1251_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1251_, 0, v_fileMap_x3f_1216_);
lean_closure_set(v___y_1251_, 1, v_declName_1213_);
lean_closure_set(v___y_1251_, 2, v_binders_1214_);
lean_closure_set(v___y_1251_, 3, v___x_1248_);
lean_closure_set(v___y_1251_, 4, v___x_1250_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1252_, v___y_1251_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v___x_1255_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1222_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1255_, 1);
v___x_1257_ = l_Lean_Core_setMessageLog___redArg(v_a_1225_, v_a_1222_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; size_t v_sz_1260_; lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1257_, 1);
v___x_1258_ = l_Lean_MessageLog_toArray(v_a_1256_);
lean_dec(v_a_1256_);
v___x_1259_ = lean_box(0);
v_sz_1260_ = lean_array_size(v___x_1258_);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1258_, v_sz_1260_, v___x_1246_, v___x_1259_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
lean_dec_ref(v___x_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1287_);
v___x_1263_ = v___x_1261_;
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v___x_1261_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1286_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1285_; 
v_fst_1265_ = lean_ctor_get(v_a_1254_, 0);
v_snd_1266_ = lean_ctor_get(v_a_1254_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1254_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1268_ = v_a_1254_;
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_a_1254_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1285_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1284_; 
v_fst_1270_ = lean_ctor_get(v_fst_1265_, 0);
v_snd_1271_ = lean_ctor_get(v_fst_1265_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_fst_1265_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1273_ = v_fst_1265_;
v_isShared_1274_ = v_isSharedCheck_1284_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_fst_1265_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1284_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_fst_1270_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_snd_1271_);
v___x_1276_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1276_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_snd_1266_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1278_);
v___x_1280_ = v___x_1263_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1254_);
v_a_1288_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1261_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1261_);
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
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_a_1256_);
lean_dec(v_a_1254_);
v_a_1296_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1257_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1257_);
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
}
else
{
lean_object* v_a_1304_; 
lean_dec(v_a_1254_);
v_a_1304_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1255_, 1);
v_a_1227_ = v_a_1304_;
goto v___jp_1226_;
}
}
else
{
lean_object* v_a_1305_; 
v_a_1305_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1253_, 1);
v_a_1227_ = v_a_1305_;
goto v___jp_1226_;
}
v___jp_1226_:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Core_setMessageLog___redArg(v_a_1225_, v_a_1222_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 0, v_a_1227_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1227_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_a_1227_);
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_fileMap_x3f_1216_);
lean_dec_ref(v_blocks_1215_);
lean_dec(v_binders_1214_);
lean_dec(v_declName_1213_);
v_a_1306_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1224_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1224_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1314_, lean_object* v_binders_1315_, lean_object* v_blocks_1316_, lean_object* v_fileMap_x3f_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1314_, v_binders_1315_, v_blocks_1316_, v_fileMap_x3f_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1326_, v___y_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v_flag_boxed_1343_; lean_object* v_res_1344_; 
v_flag_boxed_1343_ = lean_unbox(v_flag_1335_);
v_res_1344_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1343_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1345_, uint8_t v_flag_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1346_, v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_flag_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v_flag_boxed_1366_; lean_object* v_res_1367_; 
v_flag_boxed_1366_ = lean_unbox(v_flag_1357_);
v_res_1367_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1356_, v_flag_boxed_1366_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1368_, lean_object* v_msgData_1369_, uint8_t v_severity_1370_, uint8_t v_isSilent_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1368_, v_msgData_1369_, v_severity_1370_, v_isSilent_1371_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1380_, lean_object* v_msgData_1381_, lean_object* v_severity_1382_, lean_object* v_isSilent_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_severity_boxed_1391_; uint8_t v_isSilent_boxed_1392_; lean_object* v_res_1393_; 
v_severity_boxed_1391_ = lean_unbox(v_severity_1382_);
v_isSilent_boxed_1392_ = lean_unbox(v_isSilent_1383_);
v_res_1393_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1380_, v_msgData_1381_, v_severity_boxed_1391_, v_isSilent_boxed_1392_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v_ref_1380_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1394_, uint8_t v_severity_1395_, uint8_t v_isSilent_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_ref_1402_; lean_object* v___x_1403_; 
v_ref_1402_ = lean_ctor_get(v___y_1399_, 2);
v___x_1403_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1402_, v_msgData_1394_, v_severity_1395_, v_isSilent_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1404_, lean_object* v_severity_1405_, lean_object* v_isSilent_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_severity_boxed_1412_; uint8_t v_isSilent_boxed_1413_; lean_object* v_res_1414_; 
v_severity_boxed_1412_ = lean_unbox(v_severity_1405_);
v_isSilent_boxed_1413_ = lean_unbox(v_isSilent_1406_);
v_res_1414_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1404_, v_severity_boxed_1412_, v_isSilent_boxed_1413_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = 2;
v___x_1424_ = 0;
v___x_1425_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1415_, v___x_1423_, v___x_1424_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1435_, size_t v_sz_1436_, size_t v_i_1437_, lean_object* v_b_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_lt(v_i_1437_, v_sz_1436_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1438_);
return v___x_1447_;
}
else
{
lean_object* v_a_1448_; lean_object* v_snd_1449_; lean_object* v_snd_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_a_1448_ = lean_array_uget_borrowed(v_as_1435_, v_i_1437_);
v_snd_1449_ = lean_ctor_get(v_a_1448_, 1);
v_snd_1450_ = lean_ctor_get(v_snd_1449_, 1);
lean_inc(v_snd_1450_);
v___x_1451_ = l_Lean_Parser_Error_toString(v_snd_1450_);
v___x_1452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = l_Lean_MessageData_ofFormat(v___x_1452_);
v___x_1454_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1453_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
lean_dec_ref_known(v___x_1454_, 1);
v___x_1455_ = lean_box(0);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_add(v_i_1437_, v___x_1456_);
v_i_1437_ = v___x_1457_;
v_b_1438_ = v___x_1455_;
goto _start;
}
else
{
return v___x_1454_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1459_, v_sz_boxed_1470_, v_i_boxed_1471_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v_as_1459_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1490_, lean_object* v_binders_1491_, lean_object* v_docComment_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v_toCold_1501_; lean_object* v_env_1502_; lean_object* v_fileName_1503_; lean_object* v_options_1504_; lean_object* v_currNamespace_1505_; lean_object* v_openDecls_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1500_ = lean_st_ref_get(v_a_1498_);
v_toCold_1501_ = lean_ctor_get(v_a_1497_, 0);
v_env_1502_ = lean_ctor_get(v___x_1500_, 0);
lean_inc_ref_n(v_env_1502_, 2);
lean_dec(v___x_1500_);
v_fileName_1503_ = lean_ctor_get(v_toCold_1501_, 0);
v_options_1504_ = lean_ctor_get(v_toCold_1501_, 2);
v_currNamespace_1505_ = lean_ctor_get(v_toCold_1501_, 4);
v_openDecls_1506_ = lean_ctor_get(v_toCold_1501_, 5);
v___x_1507_ = lean_string_utf8_byte_size(v_docComment_1492_);
lean_inc_ref_n(v_docComment_1492_, 2);
v___x_1508_ = l_Lean_FileMap_ofString(v_docComment_1492_);
lean_inc_ref(v___x_1508_);
lean_inc_ref(v_fileName_1503_);
v___x_1509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1509_, 0, v_docComment_1492_);
lean_ctor_set(v___x_1509_, 1, v_fileName_1503_);
lean_ctor_set(v___x_1509_, 2, v___x_1508_);
lean_ctor_set(v___x_1509_, 3, v___x_1507_);
lean_inc(v_openDecls_1506_);
lean_inc(v_currNamespace_1505_);
lean_inc_ref(v_options_1504_);
v___x_1510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1510_, 0, v_env_1502_);
lean_ctor_set(v___x_1510_, 1, v_options_1504_);
lean_ctor_set(v___x_1510_, 2, v_currNamespace_1505_);
lean_ctor_set(v___x_1510_, 3, v_openDecls_1506_);
v___x_1511_ = l_Lean_Parser_mkParserState(v_docComment_1492_);
lean_dec_ref(v_docComment_1492_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1514_ = l_Lean_Parser_getTokenTable(v_env_1502_);
v___x_1515_ = l_Lean_Parser_ParserFn_run(v___x_1513_, v___x_1509_, v___x_1510_, v___x_1514_, v___x_1511_);
lean_inc_ref(v___x_1515_);
v___x_1516_ = l_Lean_Parser_ParserState_allErrors(v___x_1515_);
v___x_1517_ = lean_array_get_size(v___x_1516_);
v___x_1518_ = lean_nat_dec_eq(v___x_1517_, v___x_1512_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v___x_1515_);
lean_dec_ref(v___x_1508_);
lean_dec(v_binders_1491_);
lean_dec(v_declName_1490_);
v___x_1519_ = lean_box(0);
v_sz_1520_ = lean_array_size(v___x_1516_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1516_, v_sz_1520_, v___x_1521_, v___x_1519_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
lean_dec_ref(v___x_1516_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1530_; 
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v___x_1522_, 0);
lean_dec(v_unused_1531_);
v___x_1524_ = v___x_1522_;
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
else
{
lean_dec(v___x_1522_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1530_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1526_);
v___x_1528_ = v___x_1524_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1532_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1522_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1522_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v_stxStack_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_dec_ref(v___x_1516_);
v_stxStack_1540_ = lean_ctor_get(v___x_1515_, 0);
lean_inc_ref(v_stxStack_1540_);
lean_dec_ref(v___x_1515_);
v___x_1541_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1540_);
lean_dec_ref(v_stxStack_1540_);
v___x_1542_ = l_Lean_Syntax_getArgs(v___x_1541_);
lean_dec(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1508_);
v___x_1544_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1490_, v_binders_1491_, v___x_1542_, v___x_1543_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1545_, lean_object* v_binders_1546_, lean_object* v_docComment_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_versoDocStringOfText(v_declName_1545_, v_binders_1546_, v_docComment_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1556_, uint8_t v_severity_1557_, uint8_t v_isSilent_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1556_, v_severity_1557_, v_isSilent_1558_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1567_, lean_object* v_severity_1568_, lean_object* v_isSilent_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_severity_boxed_1577_; uint8_t v_isSilent_boxed_1578_; lean_object* v_res_1579_; 
v_severity_boxed_1577_ = lean_unbox(v_severity_1568_);
v_isSilent_boxed_1578_ = lean_unbox(v_isSilent_1569_);
v_res_1579_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1567_, v_severity_boxed_1577_, v_isSilent_boxed_1578_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_1580_, size_t v_i_1581_, lean_object* v_bs_1582_){
_start:
{
uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1581_, v_sz_1580_);
if (v___x_1583_ == 0)
{
return v_bs_1582_;
}
else
{
lean_object* v_v_1584_; lean_object* v___x_1585_; lean_object* v_bs_x27_1586_; size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_v_1584_ = lean_array_uget(v_bs_1582_, v_i_1581_);
v___x_1585_ = lean_unsigned_to_nat(0u);
v_bs_x27_1586_ = lean_array_uset(v_bs_1582_, v_i_1581_, v___x_1585_);
v___x_1587_ = ((size_t)1ULL);
v___x_1588_ = lean_usize_add(v_i_1581_, v___x_1587_);
v___x_1589_ = lean_array_uset(v_bs_x27_1586_, v_i_1581_, v_v_1584_);
v_i_1581_ = v___x_1588_;
v_bs_1582_ = v___x_1589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_1591_, lean_object* v_i_1592_, lean_object* v_bs_1593_){
_start:
{
size_t v_sz_boxed_1594_; size_t v_i_boxed_1595_; lean_object* v_res_1596_; 
v_sz_boxed_1594_ = lean_unbox_usize(v_sz_1591_);
lean_dec(v_sz_1591_);
v_i_boxed_1595_ = lean_unbox_usize(v_i_1592_);
lean_dec(v_i_1592_);
v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_1594_, v_i_boxed_1595_, v_bs_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v_suppressElabErrors_1597_, uint8_t v___x_1598_, lean_object* v_x_1599_){
_start:
{
if (lean_obj_tag(v_x_1599_) == 1)
{
lean_object* v_pre_1600_; 
v_pre_1600_ = lean_ctor_get(v_x_1599_, 0);
switch(lean_obj_tag(v_pre_1600_))
{
case 1:
{
lean_object* v_pre_1601_; 
v_pre_1601_ = lean_ctor_get(v_pre_1600_, 0);
switch(lean_obj_tag(v_pre_1601_))
{
case 0:
{
lean_object* v_str_1602_; lean_object* v_str_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v_str_1602_ = lean_ctor_get(v_x_1599_, 1);
v_str_1603_ = lean_ctor_get(v_pre_1600_, 1);
v___x_1604_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1605_ = lean_string_dec_eq(v_str_1603_, v___x_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1607_ = lean_string_dec_eq(v_str_1603_, v___x_1606_);
if (v___x_1607_ == 0)
{
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1609_ = lean_string_dec_eq(v_str_1602_, v___x_1608_);
if (v___x_1609_ == 0)
{
return v___x_1609_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
else
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1611_ = lean_string_dec_eq(v_str_1602_, v___x_1610_);
if (v___x_1611_ == 0)
{
return v___x_1611_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
case 1:
{
lean_object* v_pre_1612_; 
v_pre_1612_ = lean_ctor_get(v_pre_1601_, 0);
if (lean_obj_tag(v_pre_1612_) == 0)
{
lean_object* v_str_1613_; lean_object* v_str_1614_; lean_object* v_str_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_str_1613_ = lean_ctor_get(v_x_1599_, 1);
v_str_1614_ = lean_ctor_get(v_pre_1600_, 1);
v_str_1615_ = lean_ctor_get(v_pre_1601_, 1);
v___x_1616_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1617_ = lean_string_dec_eq(v_str_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1619_ = lean_string_dec_eq(v_str_1614_, v___x_1618_);
if (v___x_1619_ == 0)
{
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1621_ = lean_string_dec_eq(v_str_1613_, v___x_1620_);
if (v___x_1621_ == 0)
{
return v___x_1621_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
}
}
else
{
return v___x_1598_;
}
}
default: 
{
return v___x_1598_;
}
}
}
case 0:
{
lean_object* v_str_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_str_1622_ = lean_ctor_get(v_x_1599_, 1);
v___x_1623_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1624_ = lean_string_dec_eq(v_str_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
return v___x_1624_;
}
else
{
return v_suppressElabErrors_1597_;
}
}
default: 
{
return v___x_1598_;
}
}
}
else
{
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1625_, lean_object* v___x_1626_, lean_object* v_x_1627_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1628_; uint8_t v___x_11242__boxed_1629_; uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_suppressElabErrors_boxed_1628_ = lean_unbox(v_suppressElabErrors_1625_);
v___x_11242__boxed_1629_ = lean_unbox(v___x_1626_);
v_res_1630_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1628_, v___x_11242__boxed_1629_, v_x_1627_);
lean_dec(v_x_1627_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v_suppressElabErrors_1632_, uint8_t v___x_1633_, lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 1)
{
lean_object* v_pre_1635_; 
v_pre_1635_ = lean_ctor_get(v_x_1634_, 0);
switch(lean_obj_tag(v_pre_1635_))
{
case 1:
{
lean_object* v_pre_1636_; 
v_pre_1636_ = lean_ctor_get(v_pre_1635_, 0);
switch(lean_obj_tag(v_pre_1636_))
{
case 0:
{
lean_object* v_str_1637_; lean_object* v_str_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_str_1637_ = lean_ctor_get(v_x_1634_, 1);
v_str_1638_ = lean_ctor_get(v_pre_1635_, 1);
v___x_1639_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1640_ = lean_string_dec_eq(v_str_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1642_ = lean_string_dec_eq(v_str_1638_, v___x_1641_);
if (v___x_1642_ == 0)
{
return v___x_1642_;
}
else
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1644_ = lean_string_dec_eq(v_str_1637_, v___x_1643_);
if (v___x_1644_ == 0)
{
return v___x_1644_;
}
else
{
return v_suppressElabErrors_1632_;
}
}
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1646_ = lean_string_dec_eq(v_str_1637_, v___x_1645_);
if (v___x_1646_ == 0)
{
return v___x_1646_;
}
else
{
return v_suppressElabErrors_1632_;
}
}
}
case 1:
{
lean_object* v_pre_1647_; 
v_pre_1647_ = lean_ctor_get(v_pre_1636_, 0);
if (lean_obj_tag(v_pre_1647_) == 0)
{
lean_object* v_str_1648_; lean_object* v_str_1649_; lean_object* v_str_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_str_1648_ = lean_ctor_get(v_x_1634_, 1);
v_str_1649_ = lean_ctor_get(v_pre_1635_, 1);
v_str_1650_ = lean_ctor_get(v_pre_1636_, 1);
v___x_1651_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1652_ = lean_string_dec_eq(v_str_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1654_ = lean_string_dec_eq(v_str_1649_, v___x_1653_);
if (v___x_1654_ == 0)
{
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1656_ = lean_string_dec_eq(v_str_1648_, v___x_1655_);
if (v___x_1656_ == 0)
{
return v___x_1656_;
}
else
{
return v_suppressElabErrors_1632_;
}
}
}
}
else
{
return v___x_1633_;
}
}
default: 
{
return v___x_1633_;
}
}
}
case 0:
{
lean_object* v_str_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_str_1657_ = lean_ctor_get(v_x_1634_, 1);
v___x_1658_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1659_ = lean_string_dec_eq(v_str_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
return v___x_1659_;
}
else
{
return v_suppressElabErrors_1632_;
}
}
default: 
{
return v___x_1633_;
}
}
}
else
{
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1660_, lean_object* v___x_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1663_; uint8_t v___x_11306__boxed_1664_; uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_suppressElabErrors_boxed_1663_ = lean_unbox(v_suppressElabErrors_1660_);
v___x_11306__boxed_1664_ = lean_unbox(v___x_1661_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1663_, v___x_11306__boxed_1664_, v_x_1662_);
lean_dec(v_x_1662_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_1667_, lean_object* v___x_1668_, lean_object* v_as_1669_, size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_b_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_a_1677_; uint8_t v___x_1681_; 
v___x_1681_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v___x_1667_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_b_1672_);
return v___x_1682_;
}
else
{
lean_object* v_a_1683_; lean_object* v_snd_1684_; lean_object* v_toCold_1685_; lean_object* v_fst_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1744_; 
v_a_1683_ = lean_array_uget(v_as_1669_, v_i_1671_);
v_snd_1684_ = lean_ctor_get(v_a_1683_, 1);
lean_inc(v_snd_1684_);
v_toCold_1685_ = lean_ctor_get(v___y_1673_, 0);
v_fst_1686_ = lean_ctor_get(v_a_1683_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_a_1683_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_a_1683_, 1);
lean_dec(v_unused_1745_);
v___x_1688_ = v_a_1683_;
v_isShared_1689_ = v_isSharedCheck_1744_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_fst_1686_);
lean_dec(v_a_1683_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1744_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v_snd_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1742_; 
v_snd_1690_ = lean_ctor_get(v_snd_1684_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_snd_1684_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v_snd_1684_, 0);
lean_dec(v_unused_1743_);
v___x_1692_ = v_snd_1684_;
v_isShared_1693_ = v_isSharedCheck_1742_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_snd_1690_);
lean_dec(v_snd_1684_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1742_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
uint8_t v_suppressElabErrors_1694_; lean_object* v_fileName_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___y_1707_; lean_object* v___y_1708_; 
v_suppressElabErrors_1694_ = lean_ctor_get_uint8(v___y_1673_, sizeof(void*)*3 + 1);
v_fileName_1695_ = lean_ctor_get(v_toCold_1685_, 0);
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_nat_dec_eq(v___x_1668_, v___x_1697_);
lean_inc_ref(v___x_1667_);
v___x_1699_ = l_Lean_FileMap_toPosition(v___x_1667_, v_fst_1686_);
lean_dec(v_fst_1686_);
v___x_1700_ = lean_box(0);
v___x_1701_ = 2;
v___x_1702_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1703_ = l_Lean_Parser_Error_toString(v_snd_1690_);
v___x_1704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
v___x_1705_ = l_Lean_MessageData_ofFormat(v___x_1704_);
if (v_suppressElabErrors_1694_ == 0)
{
v___y_1707_ = v___y_1673_;
v___y_1708_ = v___y_1674_;
goto v___jp_1706_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___f_1740_; uint8_t v___x_1741_; 
v___x_1738_ = lean_box(v_suppressElabErrors_1694_);
v___x_1739_ = lean_box(v___x_1698_);
v___f_1740_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1740_, 0, v___x_1738_);
lean_closure_set(v___f_1740_, 1, v___x_1739_);
lean_inc_ref(v___x_1705_);
v___x_1741_ = l_Lean_MessageData_hasTag(v___f_1740_, v___x_1705_);
if (v___x_1741_ == 0)
{
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1699_);
lean_del_object(v___x_1692_);
lean_del_object(v___x_1688_);
v_a_1677_ = v___x_1696_;
goto v___jp_1676_;
}
else
{
v___y_1707_ = v___y_1673_;
v___y_1708_ = v___y_1674_;
goto v___jp_1706_;
}
}
v___jp_1706_:
{
lean_object* v___x_1709_; lean_object* v_toCold_1710_; lean_object* v_currNamespace_1711_; lean_object* v_openDecls_1712_; lean_object* v___x_1714_; 
v___x_1709_ = lean_st_ref_take(v___y_1708_);
v_toCold_1710_ = lean_ctor_get(v___y_1707_, 0);
v_currNamespace_1711_ = lean_ctor_get(v_toCold_1710_, 4);
v_openDecls_1712_ = lean_ctor_get(v_toCold_1710_, 5);
lean_inc(v_openDecls_1712_);
lean_inc(v_currNamespace_1711_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v_openDecls_1712_);
lean_ctor_set(v___x_1692_, 0, v_currNamespace_1711_);
v___x_1714_ = v___x_1692_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_currNamespace_1711_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_openDecls_1712_);
v___x_1714_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 4);
lean_ctor_set(v___x_1688_, 1, v___x_1705_);
lean_ctor_set(v___x_1688_, 0, v___x_1714_);
v___x_1716_ = v___x_1688_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1705_);
v___x_1716_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1717_; lean_object* v_env_1718_; lean_object* v_nextMacroScope_1719_; lean_object* v_ngen_1720_; lean_object* v_auxDeclNGen_1721_; lean_object* v_traceState_1722_; lean_object* v_cache_1723_; lean_object* v_messages_1724_; lean_object* v_infoState_1725_; lean_object* v_snapshotTasks_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1735_; 
lean_inc_ref(v_fileName_1695_);
v___x_1717_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1717_, 0, v_fileName_1695_);
lean_ctor_set(v___x_1717_, 1, v___x_1699_);
lean_ctor_set(v___x_1717_, 2, v___x_1700_);
lean_ctor_set(v___x_1717_, 3, v___x_1702_);
lean_ctor_set(v___x_1717_, 4, v___x_1716_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*5, v___x_1698_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*5 + 1, v___x_1701_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*5 + 2, v___x_1698_);
v_env_1718_ = lean_ctor_get(v___x_1709_, 0);
v_nextMacroScope_1719_ = lean_ctor_get(v___x_1709_, 1);
v_ngen_1720_ = lean_ctor_get(v___x_1709_, 2);
v_auxDeclNGen_1721_ = lean_ctor_get(v___x_1709_, 3);
v_traceState_1722_ = lean_ctor_get(v___x_1709_, 4);
v_cache_1723_ = lean_ctor_get(v___x_1709_, 5);
v_messages_1724_ = lean_ctor_get(v___x_1709_, 6);
v_infoState_1725_ = lean_ctor_get(v___x_1709_, 7);
v_snapshotTasks_1726_ = lean_ctor_get(v___x_1709_, 8);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1728_ = v___x_1709_;
v_isShared_1729_ = v_isSharedCheck_1735_;
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
lean_dec(v___x_1709_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1735_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = l_Lean_MessageLog_add(v___x_1717_, v_messages_1724_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 6, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_env_1718_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_nextMacroScope_1719_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_ngen_1720_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_auxDeclNGen_1721_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v_traceState_1722_);
lean_ctor_set(v_reuseFailAlloc_1734_, 5, v_cache_1723_);
lean_ctor_set(v_reuseFailAlloc_1734_, 6, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1734_, 7, v_infoState_1725_);
lean_ctor_set(v_reuseFailAlloc_1734_, 8, v_snapshotTasks_1726_);
v___x_1732_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_st_ref_put(v___y_1708_, v___x_1732_);
v_a_1677_ = v___x_1696_;
goto v___jp_1676_;
}
}
}
}
}
}
}
}
v___jp_1676_:
{
size_t v___x_1678_; size_t v___x_1679_; 
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1671_, v___x_1678_);
v_i_1671_ = v___x_1679_;
v_b_1672_ = v_a_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_as_1748_, lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
size_t v_sz_boxed_1755_; size_t v_i_boxed_1756_; lean_object* v_res_1757_; 
v_sz_boxed_1755_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1756_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1746_, v___x_1747_, v_as_1748_, v_sz_boxed_1755_, v_i_boxed_1756_, v_b_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_as_1748_);
lean_dec(v___x_1747_);
return v_res_1757_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(1);
v___x_1759_ = l_Lean_MessageData_ofFormat(v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1764_ = l_Lean_MessageData_ofFormat(v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
return v_x_1765_;
}
else
{
lean_object* v_head_1767_; lean_object* v_tail_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1790_; 
v_head_1767_ = lean_ctor_get(v_x_1766_, 0);
v_tail_1768_ = lean_ctor_get(v_x_1766_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_x_1766_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1770_ = v_x_1766_;
v_isShared_1771_ = v_isSharedCheck_1790_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_tail_1768_);
lean_inc(v_head_1767_);
lean_dec(v_x_1766_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1790_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_before_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1788_; 
v_before_1772_ = lean_ctor_get(v_head_1767_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_head_1767_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; 
v_unused_1789_ = lean_ctor_get(v_head_1767_, 1);
lean_dec(v_unused_1789_);
v___x_1774_ = v_head_1767_;
v_isShared_1775_ = v_isSharedCheck_1788_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_before_1772_);
lean_dec(v_head_1767_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1788_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1775_ == 0)
{
lean_ctor_set_tag(v___x_1774_, 7);
lean_ctor_set(v___x_1774_, 1, v___x_1776_);
lean_ctor_set(v___x_1774_, 0, v_x_1765_);
v___x_1778_ = v___x_1774_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_x_1765_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 7);
lean_ctor_set(v___x_1770_, 1, v___x_1779_);
lean_ctor_set(v___x_1770_, 0, v___x_1778_);
v___x_1781_ = v___x_1770_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = l_Lean_MessageData_ofSyntax(v_before_1772_);
v___x_1783_ = l_Lean_indentD(v___x_1782_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1781_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v_x_1765_ = v___x_1784_;
v_x_1766_ = v_tail_1768_;
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
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1795_ = l_Lean_MessageData_ofFormat(v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1796_, lean_object* v_macroStack_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_toCold_1800_; lean_object* v_options_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_toCold_1800_ = lean_ctor_get(v___y_1798_, 0);
v_options_1801_ = lean_ctor_get(v_toCold_1800_, 2);
v___x_1802_ = l_Lean_Elab_pp_macroStack;
v___x_1803_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec(v_macroStack_1797_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_msgData_1796_);
return v___x_1804_;
}
else
{
if (lean_obj_tag(v_macroStack_1797_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_msgData_1796_);
return v___x_1805_;
}
else
{
lean_object* v_head_1806_; lean_object* v_after_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1822_; 
v_head_1806_ = lean_ctor_get(v_macroStack_1797_, 0);
lean_inc(v_head_1806_);
v_after_1807_ = lean_ctor_get(v_head_1806_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_head_1806_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_head_1806_, 0);
lean_dec(v_unused_1823_);
v___x_1809_ = v_head_1806_;
v_isShared_1810_ = v_isSharedCheck_1822_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_after_1807_);
lean_dec(v_head_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1822_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 7);
lean_ctor_set(v___x_1809_, 1, v___x_1811_);
lean_ctor_set(v___x_1809_, 0, v_msgData_1796_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_msgData_1796_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v_msgData_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1814_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_MessageData_ofSyntax(v_after_1807_);
v___x_1817_ = l_Lean_indentD(v___x_1816_);
v_msgData_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1818_, 0, v___x_1815_);
lean_ctor_set(v_msgData_1818_, 1, v___x_1817_);
v___x_1819_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1818_, v_macroStack_1797_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1824_, lean_object* v_macroStack_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1824_, v_macroStack_1825_, v___y_1826_);
lean_dec_ref(v___y_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_ref_1837_; lean_object* v___x_1838_; lean_object* v_a_1839_; lean_object* v_macroStack_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_ref_1837_ = lean_ctor_get(v___y_1834_, 2);
v___x_1838_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1829_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1838_);
v_macroStack_1840_ = lean_ctor_get(v___y_1830_, 1);
v___x_1841_ = l_Lean_Elab_getBetterRef(v_ref_1837_, v_macroStack_1840_);
lean_inc(v_macroStack_1840_);
v___x_1842_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1839_, v_macroStack_1840_, v___y_1834_);
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1841_);
lean_ctor_set(v___x_1847_, 1, v_a_1843_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 1);
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1861_, lean_object* v_msg_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_toCold_1870_; lean_object* v_currRecDepth_1871_; lean_object* v_ref_1872_; uint8_t v_diag_1873_; uint8_t v_suppressElabErrors_1874_; lean_object* v_ref_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_toCold_1870_ = lean_ctor_get(v___y_1867_, 0);
v_currRecDepth_1871_ = lean_ctor_get(v___y_1867_, 1);
v_ref_1872_ = lean_ctor_get(v___y_1867_, 2);
v_diag_1873_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3);
v_suppressElabErrors_1874_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3 + 1);
v_ref_1875_ = l_Lean_replaceRef(v_ref_1861_, v_ref_1872_);
lean_inc(v_currRecDepth_1871_);
lean_inc_ref(v_toCold_1870_);
v___x_1876_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1876_, 0, v_toCold_1870_);
lean_ctor_set(v___x_1876_, 1, v_currRecDepth_1871_);
lean_ctor_set(v___x_1876_, 2, v_ref_1875_);
lean_ctor_set_uint8(v___x_1876_, sizeof(void*)*3, v_diag_1873_);
lean_ctor_set_uint8(v___x_1876_, sizeof(void*)*3 + 1, v_suppressElabErrors_1874_);
v___x_1877_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___x_1876_, v___y_1868_);
lean_dec_ref_known(v___x_1876_, 3);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1878_, v_msg_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v_ref_1878_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
uint8_t v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; uint8_t v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; uint8_t v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; uint8_t v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
lean_inc(v_docComment_1888_);
v___x_2048_ = l_Lean_Syntax_getKind(v_docComment_1888_);
v___x_2049_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2050_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2051_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2052_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2053_ = lean_name_eq(v___x_2048_, v___x_2052_);
lean_dec(v___x_2048_);
if (v___x_2053_ == 0)
{
goto v___jp_2024_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = l_Lean_Syntax_getArg(v_docComment_1888_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 1)
{
lean_object* v_kind_2056_; 
v_kind_2056_ = lean_ctor_get(v___x_2055_, 1);
lean_inc(v_kind_2056_);
if (lean_obj_tag(v_kind_2056_) == 1)
{
lean_object* v_pre_2057_; 
v_pre_2057_ = lean_ctor_get(v_kind_2056_, 0);
lean_inc(v_pre_2057_);
if (lean_obj_tag(v_pre_2057_) == 1)
{
lean_object* v_pre_2058_; 
v_pre_2058_ = lean_ctor_get(v_pre_2057_, 0);
lean_inc(v_pre_2058_);
if (lean_obj_tag(v_pre_2058_) == 1)
{
lean_object* v_pre_2059_; 
v_pre_2059_ = lean_ctor_get(v_pre_2058_, 0);
lean_inc(v_pre_2059_);
if (lean_obj_tag(v_pre_2059_) == 1)
{
lean_object* v_pre_2060_; 
v_pre_2060_ = lean_ctor_get(v_pre_2059_, 0);
lean_inc(v_pre_2060_);
if (lean_obj_tag(v_pre_2060_) == 0)
{
lean_object* v_info_2061_; lean_object* v_args_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2086_; 
v_info_2061_ = lean_ctor_get(v___x_2055_, 0);
v_args_2062_ = lean_ctor_get(v___x_2055_, 2);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2055_, 1);
lean_dec(v_unused_2087_);
v___x_2064_ = v___x_2055_;
v_isShared_2065_ = v_isSharedCheck_2086_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_args_2062_);
lean_inc(v_info_2061_);
lean_dec(v___x_2055_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2086_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_str_2066_; lean_object* v_str_2067_; lean_object* v_str_2068_; lean_object* v_str_2069_; uint8_t v___x_2070_; 
v_str_2066_ = lean_ctor_get(v_kind_2056_, 1);
lean_inc_ref(v_str_2066_);
lean_dec_ref_known(v_kind_2056_, 2);
v_str_2067_ = lean_ctor_get(v_pre_2057_, 1);
lean_inc_ref(v_str_2067_);
lean_dec_ref_known(v_pre_2057_, 2);
v_str_2068_ = lean_ctor_get(v_pre_2058_, 1);
lean_inc_ref(v_str_2068_);
lean_dec_ref_known(v_pre_2058_, 2);
v_str_2069_ = lean_ctor_get(v_pre_2059_, 1);
lean_inc_ref(v_str_2069_);
lean_dec_ref_known(v_pre_2059_, 2);
v___x_2070_ = lean_string_dec_eq(v_str_2069_, v___x_2049_);
lean_dec_ref(v_str_2069_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_str_2068_);
lean_dec_ref(v_str_2067_);
lean_dec_ref(v_str_2066_);
lean_del_object(v___x_2064_);
lean_dec_ref(v_args_2062_);
lean_dec(v_info_2061_);
goto v___jp_2024_;
}
else
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_string_dec_eq(v_str_2068_, v___x_2050_);
lean_dec_ref(v_str_2068_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_str_2067_);
lean_dec_ref(v_str_2066_);
lean_del_object(v___x_2064_);
lean_dec_ref(v_args_2062_);
lean_dec(v_info_2061_);
goto v___jp_2024_;
}
else
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_string_dec_eq(v_str_2067_, v___x_2051_);
lean_dec_ref(v_str_2067_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v_str_2066_);
lean_del_object(v___x_2064_);
lean_dec_ref(v_args_2062_);
lean_dec(v_info_2061_);
goto v___jp_2024_;
}
else
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2074_ = lean_string_dec_eq(v_str_2066_, v___x_2073_);
lean_dec_ref(v_str_2066_);
if (v___x_2074_ == 0)
{
lean_del_object(v___x_2064_);
lean_dec_ref(v_args_2062_);
lean_dec(v_info_2061_);
goto v___jp_2024_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec(v_docComment_1888_);
v___x_2075_ = l_Lean_Name_str___override(v_pre_2060_, v___x_2049_);
v___x_2076_ = l_Lean_Name_str___override(v___x_2075_, v___x_2050_);
v___x_2077_ = l_Lean_Name_str___override(v___x_2076_, v___x_2051_);
v___x_2078_ = l_Lean_Name_str___override(v___x_2077_, v___x_2073_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___x_2078_);
v___x_2080_ = v___x_2064_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_info_2061_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_args_2062_);
v___x_2080_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2081_ = lean_unsigned_to_nat(1u);
v___x_2082_ = l_Lean_Syntax_getArg(v___x_2080_, v___x_2081_);
lean_dec_ref(v___x_2080_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_2060_);
lean_dec_ref_known(v_pre_2059_, 2);
lean_dec_ref_known(v_pre_2058_, 2);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_kind_2056_, 2);
lean_dec_ref_known(v___x_2055_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_pre_2059_);
lean_dec_ref_known(v_pre_2058_, 2);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_kind_2056_, 2);
lean_dec_ref_known(v___x_2055_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_pre_2058_);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_kind_2056_, 2);
lean_dec_ref_known(v___x_2055_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec_ref_known(v_kind_2056_, 2);
lean_dec(v_pre_2057_);
lean_dec_ref_known(v___x_2055_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_kind_2056_);
lean_dec_ref_known(v___x_2055_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v___x_2055_);
goto v___jp_2024_;
}
}
v___jp_1896_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_box(0);
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
return v___x_1898_;
}
v___jp_1899_:
{
lean_object* v___x_1909_; lean_object* v_toCold_1910_; lean_object* v_currNamespace_1911_; lean_object* v_openDecls_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_env_1916_; lean_object* v_nextMacroScope_1917_; lean_object* v_ngen_1918_; lean_object* v_auxDeclNGen_1919_; lean_object* v_traceState_1920_; lean_object* v_cache_1921_; lean_object* v_messages_1922_; lean_object* v_infoState_1923_; lean_object* v_snapshotTasks_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v___x_1909_ = lean_st_ref_take(v___y_1908_);
v_toCold_1910_ = lean_ctor_get(v___y_1907_, 0);
v_currNamespace_1911_ = lean_ctor_get(v_toCold_1910_, 4);
v_openDecls_1912_ = lean_ctor_get(v_toCold_1910_, 5);
lean_inc(v_openDecls_1912_);
lean_inc(v_currNamespace_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_currNamespace_1911_);
lean_ctor_set(v___x_1913_, 1, v_openDecls_1912_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___y_1901_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1902_);
v___x_1915_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1915_, 0, v___y_1902_);
lean_ctor_set(v___x_1915_, 1, v___y_1906_);
lean_ctor_set(v___x_1915_, 2, v___y_1905_);
lean_ctor_set(v___x_1915_, 3, v___y_1903_);
lean_ctor_set(v___x_1915_, 4, v___x_1914_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5, v___y_1904_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5 + 1, v___y_1900_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5 + 2, v___y_1904_);
v_env_1916_ = lean_ctor_get(v___x_1909_, 0);
v_nextMacroScope_1917_ = lean_ctor_get(v___x_1909_, 1);
v_ngen_1918_ = lean_ctor_get(v___x_1909_, 2);
v_auxDeclNGen_1919_ = lean_ctor_get(v___x_1909_, 3);
v_traceState_1920_ = lean_ctor_get(v___x_1909_, 4);
v_cache_1921_ = lean_ctor_get(v___x_1909_, 5);
v_messages_1922_ = lean_ctor_get(v___x_1909_, 6);
v_infoState_1923_ = lean_ctor_get(v___x_1909_, 7);
v_snapshotTasks_1924_ = lean_ctor_get(v___x_1909_, 8);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1926_ = v___x_1909_;
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_snapshotTasks_1924_);
lean_inc(v_infoState_1923_);
lean_inc(v_messages_1922_);
lean_inc(v_cache_1921_);
lean_inc(v_traceState_1920_);
lean_inc(v_auxDeclNGen_1919_);
lean_inc(v_ngen_1918_);
lean_inc(v_nextMacroScope_1917_);
lean_inc(v_env_1916_);
lean_dec(v___x_1909_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1933_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = l_Lean_MessageLog_add(v___x_1915_, v_messages_1922_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 6, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_env_1916_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_nextMacroScope_1917_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_ngen_1918_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_auxDeclNGen_1919_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_traceState_1920_);
lean_ctor_set(v_reuseFailAlloc_1932_, 5, v_cache_1921_);
lean_ctor_set(v_reuseFailAlloc_1932_, 6, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1932_, 7, v_infoState_1923_);
lean_ctor_set(v_reuseFailAlloc_1932_, 8, v_snapshotTasks_1924_);
v___x_1930_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_st_ref_put(v___y_1908_, v___x_1930_);
goto v___jp_1896_;
}
}
}
v___jp_1934_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
lean_inc_ref(v___y_1941_);
v___x_1942_ = l_Lean_Parser_ParserState_allErrors(v___y_1941_);
v___x_1943_ = lean_array_get_size(v___x_1942_);
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = lean_nat_dec_eq(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; size_t v_sz_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
lean_dec_ref(v___y_1941_);
lean_dec_ref(v___y_1938_);
v___x_1946_ = lean_box(0);
v_sz_1947_ = lean_array_size(v___x_1942_);
v___x_1948_ = ((size_t)0ULL);
lean_inc_ref(v___y_1936_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1936_, v___x_1943_, v___x_1942_, v_sz_1947_, v___x_1948_, v___x_1946_, v___y_1893_, v___y_1894_);
lean_dec_ref(v___x_1942_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v___x_1949_, 0);
lean_dec(v_unused_1958_);
v___x_1951_ = v___x_1949_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v___x_1949_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_box(0);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1949_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_stxStack_1967_; lean_object* v_pos_1968_; uint8_t v___x_1969_; 
lean_dec_ref(v___x_1942_);
v_stxStack_1967_ = lean_ctor_get(v___y_1941_, 0);
lean_inc_ref(v_stxStack_1967_);
v_pos_1968_ = lean_ctor_get(v___y_1941_, 2);
lean_inc(v_pos_1968_);
lean_dec_ref(v___y_1941_);
v___x_1969_ = l_Lean_Parser_InputContext_atEnd(v___y_1938_, v_pos_1968_);
lean_dec_ref(v___y_1938_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint32_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v_stxStack_1967_);
lean_inc_ref(v___y_1936_);
v___x_1970_ = l_Lean_FileMap_toPosition(v___y_1936_, v_pos_1968_);
v___x_1971_ = lean_box(0);
v___x_1972_ = 2;
v___x_1973_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1974_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1975_ = lean_string_utf8_get(v___y_1940_, v_pos_1968_);
lean_dec(v_pos_1968_);
v___x_1976_ = lean_string_push(v___x_1973_, v___x_1975_);
v___x_1977_ = lean_string_append(v___x_1974_, v___x_1976_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1979_ = lean_string_append(v___x_1977_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
if (v___y_1939_ == 0)
{
v___y_1900_ = v___x_1972_;
v___y_1901_ = v___x_1981_;
v___y_1902_ = v___y_1937_;
v___y_1903_ = v___x_1973_;
v___y_1904_ = v___x_1969_;
v___y_1905_ = v___x_1971_;
v___y_1906_ = v___x_1970_;
v___y_1907_ = v___y_1893_;
v___y_1908_ = v___y_1894_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; uint8_t v___x_1985_; 
v___x_1982_ = lean_box(v___y_1935_);
v___x_1983_ = lean_box(v___x_1969_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1984_, 0, v___x_1982_);
lean_closure_set(v___f_1984_, 1, v___x_1983_);
lean_inc_ref(v___x_1981_);
v___x_1985_ = l_Lean_MessageData_hasTag(v___f_1984_, v___x_1981_);
if (v___x_1985_ == 0)
{
lean_dec_ref(v___x_1981_);
lean_dec_ref(v___x_1970_);
goto v___jp_1896_;
}
else
{
v___y_1900_ = v___x_1972_;
v___y_1901_ = v___x_1981_;
v___y_1902_ = v___y_1937_;
v___y_1903_ = v___x_1973_;
v___y_1904_ = v___x_1969_;
v___y_1905_ = v___x_1971_;
v___y_1906_ = v___x_1970_;
v___y_1907_ = v___y_1893_;
v___y_1908_ = v___y_1894_;
goto v___jp_1899_;
}
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_dec(v_pos_1968_);
v___x_1986_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1967_);
lean_dec_ref(v_stxStack_1967_);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
return v___x_1988_;
}
}
}
v___jp_1989_:
{
lean_object* v___x_2001_; lean_object* v_env_2002_; lean_object* v_ictx_2003_; lean_object* v_pmctx_2004_; lean_object* v_blockCtxt_2005_; lean_object* v___x_2006_; lean_object* v_s_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_s_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2001_ = lean_st_ref_get(v___y_1894_);
v_env_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref_n(v_env_2002_, 2);
lean_dec(v___x_2001_);
lean_inc(v___y_2000_);
lean_inc_ref_n(v___y_1992_, 2);
lean_inc_ref(v___y_1993_);
lean_inc_ref(v___y_1991_);
v_ictx_2003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2003_, 0, v___y_1991_);
lean_ctor_set(v_ictx_2003_, 1, v___y_1993_);
lean_ctor_set(v_ictx_2003_, 2, v___y_1992_);
lean_ctor_set(v_ictx_2003_, 3, v___y_2000_);
lean_inc(v___y_1997_);
lean_inc(v___y_1999_);
lean_inc_ref(v___y_1996_);
v_pmctx_2004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2004_, 0, v_env_2002_);
lean_ctor_set(v_pmctx_2004_, 1, v___y_1996_);
lean_ctor_set(v_pmctx_2004_, 2, v___y_1999_);
lean_ctor_set(v_pmctx_2004_, 3, v___y_1997_);
lean_inc(v___y_1995_);
v_blockCtxt_2005_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1992_, v___y_1995_, v___y_2000_);
v___x_2006_ = l_Lean_Parser_mkParserState(v___y_1991_);
lean_inc_ref(v___x_2006_);
v_s_2007_ = l_Lean_Parser_ParserState_setPos(v___x_2006_, v___y_1995_);
v___x_2008_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_2008_, 0, v_blockCtxt_2005_);
v___x_2009_ = l_Lean_Parser_getTokenTable(v_env_2002_);
lean_inc_ref(v___x_2009_);
lean_inc_ref(v_pmctx_2004_);
lean_inc_ref(v_ictx_2003_);
v_s_2010_ = l_Lean_Parser_ParserFn_run(v___x_2008_, v_ictx_2003_, v_pmctx_2004_, v___x_2009_, v_s_2007_);
lean_inc_ref(v_s_2010_);
v___x_2011_ = l_Lean_Parser_ParserState_allErrors(v_s_2010_);
v___x_2012_ = lean_array_get_size(v___x_2011_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = lean_unsigned_to_nat(0u);
v___x_2014_ = lean_nat_dec_eq(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2006_);
lean_dec_ref_known(v_pmctx_2004_, 4);
lean_dec(v___y_1994_);
v___y_1935_ = v___y_1990_;
v___y_1936_ = v___y_1992_;
v___y_1937_ = v___y_1993_;
v___y_1938_ = v_ictx_2003_;
v___y_1939_ = v___y_1998_;
v___y_1940_ = v___y_1991_;
v___y_1941_ = v_s_2010_;
goto v___jp_1934_;
}
else
{
lean_object* v_pos_2015_; uint8_t v___x_2016_; 
v_pos_2015_ = lean_ctor_get(v_s_2010_, 2);
lean_inc(v_pos_2015_);
v___x_2016_ = l_Lean_Parser_InputContext_atEnd(v_ictx_2003_, v_pos_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v_s_2010_);
v___x_2017_ = lean_box(0);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___y_1994_);
lean_ctor_set(v___x_2019_, 1, v___x_2013_);
v___x_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2013_);
lean_ctor_set(v___x_2020_, 1, v___x_2017_);
lean_ctor_set(v___x_2020_, 2, v___x_2018_);
lean_ctor_set(v___x_2020_, 3, v___x_2019_);
lean_ctor_set(v___x_2020_, 4, v___x_2013_);
v___x_2021_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_2021_, 0, v___x_2020_);
v___x_2022_ = l_Lean_Parser_ParserState_setPos(v___x_2006_, v_pos_2015_);
lean_inc_ref(v_ictx_2003_);
v___x_2023_ = l_Lean_Parser_ParserFn_run(v___x_2021_, v_ictx_2003_, v_pmctx_2004_, v___x_2009_, v___x_2022_);
v___y_1935_ = v___y_1990_;
v___y_1936_ = v___y_1992_;
v___y_1937_ = v___y_1993_;
v___y_1938_ = v_ictx_2003_;
v___y_1939_ = v___y_1998_;
v___y_1940_ = v___y_1991_;
v___y_1941_ = v___x_2023_;
goto v___jp_1934_;
}
else
{
lean_dec(v_pos_2015_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2006_);
lean_dec_ref_known(v_pmctx_2004_, 4);
lean_dec(v___y_1994_);
v___y_1935_ = v___y_1990_;
v___y_1936_ = v___y_1992_;
v___y_1937_ = v___y_1993_;
v___y_1938_ = v_ictx_2003_;
v___y_1939_ = v___y_1998_;
v___y_1940_ = v___y_1991_;
v___y_1941_ = v_s_2010_;
goto v___jp_1934_;
}
}
}
v___jp_2024_:
{
lean_object* v_toCold_2025_; uint8_t v_suppressElabErrors_2026_; lean_object* v_fileName_2027_; lean_object* v_fileMap_2028_; lean_object* v_options_2029_; lean_object* v_currNamespace_2030_; lean_object* v_openDecls_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; 
v_toCold_2025_ = lean_ctor_get(v___y_1893_, 0);
v_suppressElabErrors_2026_ = lean_ctor_get_uint8(v___y_1893_, sizeof(void*)*3 + 1);
v_fileName_2027_ = lean_ctor_get(v_toCold_2025_, 0);
v_fileMap_2028_ = lean_ctor_get(v_toCold_2025_, 1);
v_options_2029_ = lean_ctor_get(v_toCold_2025_, 2);
v_currNamespace_2030_ = lean_ctor_get(v_toCold_2025_, 4);
v_openDecls_2031_ = lean_ctor_get(v_toCold_2025_, 5);
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = l_Lean_Syntax_getArg(v_docComment_1888_, v___x_2032_);
v___x_2034_ = 1;
v___x_2035_ = l_Lean_Syntax_getPos_x3f(v___x_2033_, v___x_2034_);
if (lean_obj_tag(v___x_2035_) == 1)
{
lean_object* v_val_2036_; lean_object* v___x_2037_; 
v_val_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v___x_2037_ = l_Lean_Syntax_getTailPos_x3f(v___x_2033_, v___x_2034_);
lean_dec(v___x_2033_);
if (lean_obj_tag(v___x_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v_source_2039_; lean_object* v___x_2040_; lean_object* v_endPos_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
lean_dec(v_docComment_1888_);
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v_source_2039_ = lean_ctor_get(v_fileMap_2028_, 0);
v___x_2040_ = lean_string_utf8_prev(v_source_2039_, v_val_2038_);
lean_dec(v_val_2038_);
v_endPos_2041_ = lean_string_utf8_prev(v_source_2039_, v___x_2040_);
lean_dec(v___x_2040_);
v___x_2042_ = lean_string_utf8_byte_size(v_source_2039_);
v___x_2043_ = lean_nat_dec_le(v_endPos_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v_endPos_2041_);
v___y_1990_ = v_suppressElabErrors_2026_;
v___y_1991_ = v_source_2039_;
v___y_1992_ = v_fileMap_2028_;
v___y_1993_ = v_fileName_2027_;
v___y_1994_ = v___x_2032_;
v___y_1995_ = v_val_2036_;
v___y_1996_ = v_options_2029_;
v___y_1997_ = v_openDecls_2031_;
v___y_1998_ = v_suppressElabErrors_2026_;
v___y_1999_ = v_currNamespace_2030_;
v___y_2000_ = v___x_2042_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v_suppressElabErrors_2026_;
v___y_1991_ = v_source_2039_;
v___y_1992_ = v_fileMap_2028_;
v___y_1993_ = v_fileName_2027_;
v___y_1994_ = v___x_2032_;
v___y_1995_ = v_val_2036_;
v___y_1996_ = v_options_2029_;
v___y_1997_ = v_openDecls_2031_;
v___y_1998_ = v_suppressElabErrors_2026_;
v___y_1999_ = v_currNamespace_2030_;
v___y_2000_ = v_endPos_2041_;
goto v___jp_1989_;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v___x_2037_);
lean_dec(v_val_2036_);
v___x_2044_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2045_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1888_, v___x_2044_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v_docComment_1888_);
return v___x_2045_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v___x_2035_);
lean_dec(v___x_2033_);
v___x_2046_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2047_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1888_, v___x_2046_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v_docComment_1888_);
return v___x_2047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2110_, lean_object* v_binders_2111_, lean_object* v_docComment_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v_body_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_unsigned_to_nat(1u);
v_body_2121_ = l_Lean_Syntax_getArg(v_docComment_2112_, v___x_2120_);
v___x_2122_ = 1;
v___x_2123_ = l_Lean_Syntax_getPos_x3f(v_body_2121_, v___x_2122_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2121_);
v___x_2125_ = l_Lean_Syntax_isOfKind(v_body_2121_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
lean_dec(v_body_2121_);
v___x_2126_ = l_Lean_TSyntax_getDocString(v_docComment_2112_);
lean_dec(v_docComment_2112_);
v___x_2127_ = l_Lean_versoDocStringOfText(v_declName_2110_, v_binders_2111_, v___x_2126_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
lean_dec(v_docComment_2112_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = l_Lean_Syntax_getArg(v_body_2121_, v___x_2128_);
lean_dec(v_body_2121_);
v___x_2130_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2129_);
v___x_2131_ = l_Lean_Syntax_isOfKind(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_Syntax_getArgs(v___x_2129_);
lean_dec(v___x_2129_);
v___x_2133_ = lean_box(0);
v___x_2134_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2110_, v_binders_2111_, v___x_2132_, v___x_2133_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = l_Lean_Syntax_getArg(v___x_2129_, v___x_2128_);
lean_dec(v___x_2129_);
v___x_2136_ = l_Lean_Syntax_getAtomVal(v___x_2135_);
lean_dec(v___x_2135_);
v___x_2137_ = l_Lean_versoDocStringOfText(v_declName_2110_, v_binders_2111_, v___x_2136_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2137_;
}
}
}
else
{
lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2123_, 1);
lean_dec(v_body_2121_);
v___x_2138_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2189_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2189_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2189_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
if (lean_obj_tag(v_a_2139_) == 1)
{
lean_object* v_val_2143_; lean_object* v___x_2144_; size_t v_sz_2145_; size_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; 
lean_del_object(v___x_2141_);
v_val_2143_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v_a_2139_, 1);
v___x_2144_ = l_Lean_Syntax_getArgs(v_val_2143_);
lean_dec(v_val_2143_);
v_sz_2145_ = lean_array_size(v___x_2144_);
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2145_, v___x_2146_, v___x_2144_);
v___x_2148_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2148_, 0, v___x_2147_);
v___x_2149_ = 0;
v___x_2150_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2110_, v_binders_2111_, v___x_2148_, v___x_2149_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2176_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2176_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2176_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v_fst_2155_; lean_object* v_snd_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2175_; 
v_fst_2155_ = lean_ctor_get(v_a_2151_, 0);
v_snd_2156_ = lean_ctor_get(v_a_2151_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2151_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2158_ = v_a_2151_;
v_isShared_2159_ = v_isSharedCheck_2175_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_snd_2156_);
lean_inc(v_fst_2155_);
lean_dec(v_a_2151_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2175_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_fst_2160_; lean_object* v_snd_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2174_; 
v_fst_2160_ = lean_ctor_get(v_fst_2155_, 0);
v_snd_2161_ = lean_ctor_get(v_fst_2155_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_fst_2155_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2163_ = v_fst_2155_;
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_snd_2161_);
lean_inc(v_fst_2160_);
lean_dec(v_fst_2155_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_fst_2160_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_snd_2161_);
v___x_2166_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2166_);
v___x_2168_ = v___x_2158_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_snd_2156_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2168_);
v___x_2170_ = v___x_2153_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_a_2177_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2150_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2150_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
lean_dec(v_a_2139_);
lean_dec(v_binders_2111_);
lean_dec(v_declName_2110_);
v___x_2185_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2185_);
v___x_2187_ = v___x_2141_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
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
lean_dec(v_binders_2111_);
lean_dec(v_declName_2110_);
v_a_2190_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2138_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2138_);
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
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2198_, lean_object* v_binders_2199_, lean_object* v_docComment_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_versoDocString(v_declName_2198_, v_binders_2199_, v_docComment_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2209_, lean_object* v___x_2210_, lean_object* v_as_2211_, size_t v_sz_2212_, size_t v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2209_, v___x_2210_, v_as_2211_, v_sz_2212_, v_i_2213_, v_b_2214_, v___y_2219_, v___y_2220_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2223_, lean_object* v___x_2224_, lean_object* v_as_2225_, lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
size_t v_sz_boxed_2236_; size_t v_i_boxed_2237_; lean_object* v_res_2238_; 
v_sz_boxed_2236_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2237_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2223_, v___x_2224_, v_as_2225_, v_sz_boxed_2236_, v_i_boxed_2237_, v_b_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_as_2225_);
lean_dec(v___x_2224_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2239_, lean_object* v_ref_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2240_, v_msg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2250_, lean_object* v_ref_2251_, lean_object* v_msg_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2250_, v_ref_2251_, v_msg_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v_ref_2251_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2261_, lean_object* v_msg_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2271_, v_msg_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2281_, lean_object* v_macroStack_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2281_, v_macroStack_2282_, v___y_2287_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2291_, lean_object* v_macroStack_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2291_, v_macroStack_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2301_, lean_object* v_doc_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2318_; lean_object* v_env_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2310_ = lean_st_ref_get(v_a_2308_);
v_env_2325_ = lean_ctor_get(v___x_2310_, 0);
lean_inc_ref(v_env_2325_);
lean_dec(v___x_2310_);
v___x_2326_ = l_Lean_getMainVersoModuleDocs(v_env_2325_);
v___x_2327_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2326_);
lean_dec_ref(v___x_2326_);
if (lean_obj_tag(v___x_2327_) == 0)
{
v___y_2318_ = v___x_2327_;
goto v___jp_2317_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2337_; 
v_val_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_val_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2337_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_add(v_val_2328_, v___x_2332_);
lean_dec(v_val_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2333_);
v___x_2335_ = v___x_2330_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
v___y_2318_ = v___x_2335_;
goto v___jp_2317_;
}
}
}
v___jp_2311_:
{
lean_object* v___x_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2314_, 0, v_range_2301_);
lean_closure_set(v___x_2314_, 1, v___y_2312_);
lean_closure_set(v___x_2314_, 2, v___y_2313_);
v___x_2315_ = 0;
v___x_2316_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2314_, v___x_2315_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2316_;
}
v___jp_2317_:
{
lean_object* v___x_2319_; size_t v_sz_2320_; size_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = l_Lean_Syntax_getArgs(v_doc_2302_);
v_sz_2320_ = lean_array_size(v___x_2319_);
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2320_, v___x_2321_, v___x_2319_);
if (lean_obj_tag(v___y_2318_) == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_unsigned_to_nat(0u);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v___x_2323_;
goto v___jp_2311_;
}
else
{
lean_object* v_val_2324_; 
v_val_2324_ = lean_ctor_get(v___y_2318_, 0);
lean_inc(v_val_2324_);
lean_dec_ref_known(v___y_2318_, 1);
v___y_2312_ = v___x_2322_;
v___y_2313_ = v_val_2324_;
goto v___jp_2311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2338_, lean_object* v_doc_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_versoModDocString(v_range_2338_, v_doc_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_doc_2339_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2357_, lean_object* v_docComment_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2367_ = l_Lean_versoDocStringOfText(v_declName_2357_, v___x_2366_, v_docComment_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2368_, lean_object* v_docComment_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_versoDocStringFromString(v_declName_2368_, v_docComment_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2378_, lean_object* v_declName_2379_, lean_object* v_env_2380_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = l_Lean_docStringExt;
v___x_2382_ = l_String_removeLeadingSpaces(v_docString_2378_);
v___x_2383_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2381_, v_env_2380_, v_declName_2379_, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2384_, lean_object* v_modifyEnv_2385_, lean_object* v_docString_2386_){
_start:
{
lean_object* v___f_2387_; lean_object* v___x_2388_; 
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2387_, 0, v_docString_2386_);
lean_closure_set(v___f_2387_, 1, v_declName_2384_);
v___x_2388_ = lean_apply_1(v_modifyEnv_2385_, v___f_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_docComment_2391_, lean_object* v_toBind_2392_, lean_object* v___f_2393_, lean_object* v_____r_2394_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = l_Lean_getDocStringText___redArg(v_inst_2389_, v_inst_2390_, v_docComment_2391_);
v___x_2396_ = lean_apply_4(v_toBind_2392_, lean_box(0), lean_box(0), v___x_2395_, v___f_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_docComment_2402_, lean_object* v_toBind_2403_, lean_object* v___f_2404_, lean_object* v_____r_2405_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = l_Lean_validateDocComment___redArg(v_inst_2397_, v_inst_2398_, v_inst_2399_, v_inst_2400_, v_inst_2401_, v_docComment_2402_);
v___x_2407_ = lean_apply_4(v_toBind_2403_, lean_box(0), lean_box(0), v___x_2406_, v___f_2404_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_inst_2412_, lean_object* v_docComment_2413_, lean_object* v_toBind_2414_, lean_object* v___f_2415_, lean_object* v_____r_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2408_, v_inst_2409_, v_inst_2410_, v_inst_2411_, v_inst_2412_, v_docComment_2413_, v_toBind_2414_, v___f_2415_, v_____r_2416_);
lean_dec(v_docComment_2413_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2418_, lean_object* v_____r_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_apply_1(v___f_2418_, v_____r_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2427_, lean_object* v_declName_2428_, uint8_t v___x_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_toBind_2432_, lean_object* v___f_2433_, lean_object* v_____do__lift_2434_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2434_, v_declName_2428_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_dec(v___f_2433_);
lean_dec(v_toBind_2432_);
lean_dec_ref(v_inst_2431_);
lean_dec_ref(v_inst_2430_);
lean_dec(v_declName_2428_);
goto v___jp_2435_;
}
else
{
lean_dec_ref_known(v___x_2438_, 1);
if (v___x_2429_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_dec(v___f_2427_);
v___x_2439_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2440_ = l_Lean_MessageData_ofConstName(v_declName_2428_, v___x_2429_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_throwError___redArg(v_inst_2430_, v_inst_2431_, v___x_2443_);
v___x_2445_ = lean_apply_4(v_toBind_2432_, lean_box(0), lean_box(0), v___x_2444_, v___f_2433_);
return v___x_2445_;
}
else
{
lean_dec(v___f_2433_);
lean_dec(v_toBind_2432_);
lean_dec_ref(v_inst_2431_);
lean_dec_ref(v_inst_2430_);
lean_dec(v_declName_2428_);
goto v___jp_2435_;
}
}
v___jp_2435_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_apply_1(v___f_2427_, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2446_, lean_object* v_declName_2447_, lean_object* v___x_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_toBind_2451_, lean_object* v___f_2452_, lean_object* v_____do__lift_2453_){
_start:
{
uint8_t v___x_243__boxed_2454_; lean_object* v_res_2455_; 
v___x_243__boxed_2454_ = lean_unbox(v___x_2448_);
v_res_2455_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2446_, v_declName_2447_, v___x_243__boxed_2454_, v_inst_2449_, v_inst_2450_, v_toBind_2451_, v___f_2452_, v_____do__lift_2453_);
lean_dec_ref(v_____do__lift_2453_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_declName_2463_, lean_object* v_docComment_2464_){
_start:
{
lean_object* v_toApplicative_2465_; lean_object* v_toBind_2466_; lean_object* v_toPure_2467_; uint8_t v___x_2468_; 
v_toApplicative_2465_ = lean_ctor_get(v_inst_2456_, 0);
v_toBind_2466_ = lean_ctor_get(v_inst_2456_, 1);
lean_inc(v_toBind_2466_);
v_toPure_2467_ = lean_ctor_get(v_toApplicative_2465_, 1);
v___x_2468_ = l_Lean_Name_isAnonymous(v_declName_2463_);
if (v___x_2468_ == 0)
{
lean_object* v_getEnv_2469_; lean_object* v_modifyEnv_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; 
v_getEnv_2469_ = lean_ctor_get(v_inst_2459_, 0);
lean_inc(v_getEnv_2469_);
v_modifyEnv_2470_ = lean_ctor_get(v_inst_2459_, 1);
lean_inc(v_modifyEnv_2470_);
lean_dec_ref(v_inst_2459_);
lean_inc(v_declName_2463_);
v___f_2471_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2471_, 0, v_declName_2463_);
lean_closure_set(v___f_2471_, 1, v_modifyEnv_2470_);
lean_inc_n(v_toBind_2466_, 3);
lean_inc(v_docComment_2464_);
lean_inc_ref(v_inst_2460_);
lean_inc_ref_n(v_inst_2456_, 2);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2472_, 0, v_inst_2456_);
lean_closure_set(v___f_2472_, 1, v_inst_2460_);
lean_closure_set(v___f_2472_, 2, v_docComment_2464_);
lean_closure_set(v___f_2472_, 3, v_toBind_2466_);
lean_closure_set(v___f_2472_, 4, v___f_2471_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2473_, 0, v_inst_2456_);
lean_closure_set(v___f_2473_, 1, v_inst_2457_);
lean_closure_set(v___f_2473_, 2, v_inst_2461_);
lean_closure_set(v___f_2473_, 3, v_inst_2462_);
lean_closure_set(v___f_2473_, 4, v_inst_2458_);
lean_closure_set(v___f_2473_, 5, v_docComment_2464_);
lean_closure_set(v___f_2473_, 6, v_toBind_2466_);
lean_closure_set(v___f_2473_, 7, v___f_2472_);
lean_inc_ref(v___f_2473_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2474_, 0, v___f_2473_);
v___x_2475_ = lean_box(v___x_2468_);
v___f_2476_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2476_, 0, v___f_2473_);
lean_closure_set(v___f_2476_, 1, v_declName_2463_);
lean_closure_set(v___f_2476_, 2, v___x_2475_);
lean_closure_set(v___f_2476_, 3, v_inst_2456_);
lean_closure_set(v___f_2476_, 4, v_inst_2460_);
lean_closure_set(v___f_2476_, 5, v_toBind_2466_);
lean_closure_set(v___f_2476_, 6, v___f_2474_);
v___x_2477_ = lean_apply_4(v_toBind_2466_, lean_box(0), lean_box(0), v_getEnv_2469_, v___f_2476_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_inc(v_toPure_2467_);
lean_dec(v_toBind_2466_);
lean_dec(v_docComment_2464_);
lean_dec(v_declName_2463_);
lean_dec(v_inst_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_inst_2460_);
lean_dec_ref(v_inst_2459_);
lean_dec(v_inst_2458_);
lean_dec(v_inst_2457_);
lean_dec_ref(v_inst_2456_);
v___x_2478_ = lean_box(0);
v___x_2479_ = lean_apply_2(v_toPure_2467_, lean_box(0), v___x_2478_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_declName_2488_, lean_object* v_docComment_2489_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_addMarkdownDocString___redArg(v_inst_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_inst_2486_, v_inst_2487_, v_declName_2488_, v_docComment_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2491_, lean_object* v_x1_2492_, lean_object* v_x2_2493_){
_start:
{
lean_object* v_index_2494_; lean_object* v_sourceString_2495_; lean_object* v_imports_2496_; lean_object* v_currNamespace_2497_; lean_object* v_openDecls_2498_; lean_object* v_options_2499_; lean_object* v_check_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2513_; 
v_index_2494_ = lean_ctor_get(v_x2_2493_, 1);
v_sourceString_2495_ = lean_ctor_get(v_x2_2493_, 2);
v_imports_2496_ = lean_ctor_get(v_x2_2493_, 3);
v_currNamespace_2497_ = lean_ctor_get(v_x2_2493_, 4);
v_openDecls_2498_ = lean_ctor_get(v_x2_2493_, 5);
v_options_2499_ = lean_ctor_get(v_x2_2493_, 6);
v_check_2500_ = lean_ctor_get(v_x2_2493_, 7);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_x2_2493_);
if (v_isSharedCheck_2513_ == 0)
{
lean_object* v_unused_2514_; 
v_unused_2514_ = lean_ctor_get(v_x2_2493_, 0);
lean_dec(v_unused_2514_);
v___x_2502_ = v_x2_2493_;
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_check_2500_);
lean_inc(v_options_2499_);
lean_inc(v_openDecls_2498_);
lean_inc(v_currNamespace_2497_);
lean_inc(v_imports_2496_);
lean_inc(v_sourceString_2495_);
lean_inc(v_index_2494_);
lean_dec(v_x2_2493_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2513_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2504_; lean_object* v_toEnvExtension_2505_; lean_object* v_asyncMode_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v___x_2504_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2505_ = lean_ctor_get(v___x_2504_, 0);
v_asyncMode_2506_ = lean_ctor_get(v_toEnvExtension_2505_, 2);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_declName_2491_);
if (v_isShared_2503_ == 0)
{
lean_ctor_set(v___x_2502_, 0, v___x_2507_);
v___x_2509_ = v___x_2502_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_index_2494_);
lean_ctor_set(v_reuseFailAlloc_2512_, 2, v_sourceString_2495_);
lean_ctor_set(v_reuseFailAlloc_2512_, 3, v_imports_2496_);
lean_ctor_set(v_reuseFailAlloc_2512_, 4, v_currNamespace_2497_);
lean_ctor_set(v_reuseFailAlloc_2512_, 5, v_openDecls_2498_);
lean_ctor_set(v_reuseFailAlloc_2512_, 6, v_options_2499_);
lean_ctor_set(v_reuseFailAlloc_2512_, 7, v_check_2500_);
v___x_2509_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2504_, v_x1_2492_, v___x_2509_, v_asyncMode_2506_, v___x_2510_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2534_, lean_object* v_docs_2535_, lean_object* v_deferred_2536_, lean_object* v___f_2537_, lean_object* v_env_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v_env_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2539_ = l_Lean_versoDocStringExt;
v_env_2540_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2539_, v_env_2538_, v_declName_2534_, v_docs_2535_);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_array_get_size(v_deferred_2536_);
v___x_2543_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2544_ = lean_nat_dec_lt(v___x_2541_, v___x_2542_);
if (v___x_2544_ == 0)
{
lean_dec_ref(v___f_2537_);
lean_dec_ref(v_deferred_2536_);
return v_env_2540_;
}
else
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_nat_dec_le(v___x_2542_, v___x_2542_);
if (v___x_2545_ == 0)
{
if (v___x_2544_ == 0)
{
lean_dec_ref(v___f_2537_);
lean_dec_ref(v_deferred_2536_);
return v_env_2540_;
}
else
{
size_t v___x_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = lean_usize_of_nat(v___x_2542_);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2543_, v___f_2537_, v_deferred_2536_, v___x_2546_, v___x_2547_, v_env_2540_);
return v___x_2548_;
}
}
else
{
size_t v___x_2549_; size_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = lean_usize_of_nat(v___x_2542_);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2543_, v___f_2537_, v_deferred_2536_, v___x_2549_, v___x_2550_, v_env_2540_);
return v___x_2551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2552_, lean_object* v___f_2553_, lean_object* v_____r_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_apply_1(v_modifyEnv_2552_, v___f_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2558_, lean_object* v_modifyEnv_2559_, lean_object* v___f_2560_, uint8_t v___x_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_toBind_2564_, lean_object* v___f_2565_, lean_object* v_____do__lift_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2566_, v_declName_2558_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec(v___f_2565_);
lean_dec(v_toBind_2564_);
lean_dec_ref(v_inst_2563_);
lean_dec_ref(v_inst_2562_);
lean_dec(v_declName_2558_);
v___x_2568_ = lean_apply_1(v_modifyEnv_2559_, v___f_2560_);
return v___x_2568_;
}
else
{
lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2585_; 
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2586_);
v___x_2570_ = v___x_2567_;
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2567_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
if (v___x_2561_ == 0)
{
lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
lean_dec_ref(v___f_2560_);
lean_dec(v_modifyEnv_2559_);
v___x_2572_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2573_ = 1;
v___x_2574_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2558_, v___x_2573_);
v___x_2575_ = lean_string_append(v___x_2572_, v___x_2574_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2577_ = lean_string_append(v___x_2575_, v___x_2576_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 3);
lean_ctor_set(v___x_2570_, 0, v___x_2577_);
v___x_2579_ = v___x_2570_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2580_ = l_Lean_MessageData_ofFormat(v___x_2579_);
v___x_2581_ = l_Lean_throwError___redArg(v_inst_2562_, v_inst_2563_, v___x_2580_);
v___x_2582_ = lean_apply_4(v_toBind_2564_, lean_box(0), lean_box(0), v___x_2581_, v___f_2565_);
return v___x_2582_;
}
}
else
{
lean_object* v___x_2584_; 
lean_del_object(v___x_2570_);
lean_dec(v___f_2565_);
lean_dec(v_toBind_2564_);
lean_dec_ref(v_inst_2563_);
lean_dec_ref(v_inst_2562_);
lean_dec(v_declName_2558_);
v___x_2584_ = lean_apply_1(v_modifyEnv_2559_, v___f_2560_);
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2587_, lean_object* v_modifyEnv_2588_, lean_object* v___f_2589_, lean_object* v___x_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_toBind_2593_, lean_object* v___f_2594_, lean_object* v_____do__lift_2595_){
_start:
{
uint8_t v___x_371__boxed_2596_; lean_object* v_res_2597_; 
v___x_371__boxed_2596_ = lean_unbox(v___x_2590_);
v_res_2597_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2587_, v_modifyEnv_2588_, v___f_2589_, v___x_371__boxed_2596_, v_inst_2591_, v_inst_2592_, v_toBind_2593_, v___f_2594_, v_____do__lift_2595_);
lean_dec_ref(v_____do__lift_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_inst_2600_, lean_object* v_declName_2601_, lean_object* v_docs_2602_, lean_object* v_deferred_2603_){
_start:
{
lean_object* v_toApplicative_2604_; lean_object* v_toBind_2605_; lean_object* v_toPure_2606_; uint8_t v___x_2607_; 
v_toApplicative_2604_ = lean_ctor_get(v_inst_2598_, 0);
v_toBind_2605_ = lean_ctor_get(v_inst_2598_, 1);
lean_inc(v_toBind_2605_);
v_toPure_2606_ = lean_ctor_get(v_toApplicative_2604_, 1);
v___x_2607_ = l_Lean_Name_isAnonymous(v_declName_2601_);
if (v___x_2607_ == 0)
{
lean_object* v_getEnv_2608_; lean_object* v_modifyEnv_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; 
v_getEnv_2608_ = lean_ctor_get(v_inst_2599_, 0);
lean_inc(v_getEnv_2608_);
v_modifyEnv_2609_ = lean_ctor_get(v_inst_2599_, 1);
lean_inc_n(v_modifyEnv_2609_, 2);
lean_dec_ref(v_inst_2599_);
lean_inc_n(v_declName_2601_, 2);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2610_, 0, v_declName_2601_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2611_, 0, v_declName_2601_);
lean_closure_set(v___f_2611_, 1, v_docs_2602_);
lean_closure_set(v___f_2611_, 2, v_deferred_2603_);
lean_closure_set(v___f_2611_, 3, v___f_2610_);
lean_inc_ref(v___f_2611_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2612_, 0, v_modifyEnv_2609_);
lean_closure_set(v___f_2612_, 1, v___f_2611_);
v___x_2613_ = lean_box(v___x_2607_);
lean_inc(v_toBind_2605_);
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2614_, 0, v_declName_2601_);
lean_closure_set(v___f_2614_, 1, v_modifyEnv_2609_);
lean_closure_set(v___f_2614_, 2, v___f_2611_);
lean_closure_set(v___f_2614_, 3, v___x_2613_);
lean_closure_set(v___f_2614_, 4, v_inst_2598_);
lean_closure_set(v___f_2614_, 5, v_inst_2600_);
lean_closure_set(v___f_2614_, 6, v_toBind_2605_);
lean_closure_set(v___f_2614_, 7, v___f_2612_);
v___x_2615_ = lean_apply_4(v_toBind_2605_, lean_box(0), lean_box(0), v_getEnv_2608_, v___f_2614_);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_inc(v_toPure_2606_);
lean_dec(v_toBind_2605_);
lean_dec_ref(v_deferred_2603_);
lean_dec_ref(v_docs_2602_);
lean_dec(v_declName_2601_);
lean_dec_ref(v_inst_2600_);
lean_dec_ref(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_apply_2(v_toPure_2606_, lean_box(0), v___x_2616_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_declName_2623_, lean_object* v_docs_2624_, lean_object* v_deferred_2625_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2619_, v_inst_2620_, v_inst_2622_, v_declName_2623_, v_docs_2624_, v_deferred_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_declName_2632_, lean_object* v_docs_2633_, lean_object* v_deferred_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_addVersoDocStringCore(v_m_2627_, v_inst_2628_, v_inst_2629_, v_inst_2630_, v_inst_2631_, v_declName_2632_, v_docs_2633_, v_deferred_2634_);
lean_dec(v_inst_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2636_, lean_object* v_x1_2637_, lean_object* v_x2_2638_){
_start:
{
lean_object* v_index_2639_; lean_object* v_sourceString_2640_; lean_object* v_imports_2641_; lean_object* v_currNamespace_2642_; lean_object* v_openDecls_2643_; lean_object* v_options_2644_; lean_object* v_check_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2658_; 
v_index_2639_ = lean_ctor_get(v_x2_2638_, 1);
v_sourceString_2640_ = lean_ctor_get(v_x2_2638_, 2);
v_imports_2641_ = lean_ctor_get(v_x2_2638_, 3);
v_currNamespace_2642_ = lean_ctor_get(v_x2_2638_, 4);
v_openDecls_2643_ = lean_ctor_get(v_x2_2638_, 5);
v_options_2644_ = lean_ctor_get(v_x2_2638_, 6);
v_check_2645_ = lean_ctor_get(v_x2_2638_, 7);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_x2_2638_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; 
v_unused_2659_ = lean_ctor_get(v_x2_2638_, 0);
lean_dec(v_unused_2659_);
v___x_2647_ = v_x2_2638_;
v_isShared_2648_ = v_isSharedCheck_2658_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_check_2645_);
lean_inc(v_options_2644_);
lean_inc(v_openDecls_2643_);
lean_inc(v_currNamespace_2642_);
lean_inc(v_imports_2641_);
lean_inc(v_sourceString_2640_);
lean_inc(v_index_2639_);
lean_dec(v_x2_2638_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2658_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v_toEnvExtension_2650_; lean_object* v_asyncMode_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2649_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2650_ = lean_ctor_get(v___x_2649_, 0);
v_asyncMode_2651_ = lean_ctor_get(v_toEnvExtension_2650_, 2);
v___x_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_size_2636_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2652_);
v___x_2654_ = v___x_2647_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_index_2639_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_sourceString_2640_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_imports_2641_);
lean_ctor_set(v_reuseFailAlloc_2657_, 4, v_currNamespace_2642_);
lean_ctor_set(v_reuseFailAlloc_2657_, 5, v_openDecls_2643_);
lean_ctor_set(v_reuseFailAlloc_2657_, 6, v_options_2644_);
lean_ctor_set(v_reuseFailAlloc_2657_, 7, v_check_2645_);
v___x_2654_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_box(0);
v___x_2656_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2649_, v_x1_2637_, v___x_2654_, v_asyncMode_2651_, v___x_2655_);
return v___x_2656_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_deferred_2666_, lean_object* v_inst_2667_, lean_object* v___f_2668_, lean_object* v_____do__lift_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2669_, v_docs_2663_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec_ref(v___f_2668_);
lean_dec_ref(v_inst_2667_);
lean_dec_ref(v_deferred_2666_);
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2673_ = l_Lean_stringToMessageData(v_a_2671_);
v___x_2674_ = l_Lean_indentD(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2672_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_throwError___redArg(v_inst_2664_, v_inst_2665_, v___x_2675_);
return v___x_2676_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
lean_dec_ref(v_inst_2665_);
lean_dec_ref(v_inst_2664_);
v_a_2677_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2678_ = lean_unsigned_to_nat(0u);
v___x_2679_ = lean_array_get_size(v_deferred_2666_);
v___x_2680_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2681_ = lean_nat_dec_lt(v___x_2678_, v___x_2679_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
lean_dec_ref(v___f_2668_);
lean_dec_ref(v_deferred_2666_);
v___x_2682_ = l_Lean_setEnv___redArg(v_inst_2667_, v_a_2677_);
return v___x_2682_;
}
else
{
uint8_t v___x_2683_; 
v___x_2683_ = lean_nat_dec_le(v___x_2679_, v___x_2679_);
if (v___x_2683_ == 0)
{
if (v___x_2681_ == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref(v___f_2668_);
lean_dec_ref(v_deferred_2666_);
v___x_2684_ = l_Lean_setEnv___redArg(v_inst_2667_, v_a_2677_);
return v___x_2684_;
}
else
{
size_t v___x_2685_; size_t v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2685_ = ((size_t)0ULL);
v___x_2686_ = lean_usize_of_nat(v___x_2679_);
v___x_2687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2680_, v___f_2668_, v_deferred_2666_, v___x_2685_, v___x_2686_, v_a_2677_);
v___x_2688_ = l_Lean_setEnv___redArg(v_inst_2667_, v___x_2687_);
return v___x_2688_;
}
}
else
{
size_t v___x_2689_; size_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = ((size_t)0ULL);
v___x_2690_ = lean_usize_of_nat(v___x_2679_);
v___x_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2680_, v___f_2668_, v_deferred_2666_, v___x_2689_, v___x_2690_, v_a_2677_);
v___x_2692_ = l_Lean_setEnv___redArg(v_inst_2667_, v___x_2691_);
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_deferred_2696_, lean_object* v_inst_2697_, lean_object* v_toBind_2698_, lean_object* v_getEnv_2699_, lean_object* v_____do__lift_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v_size_2702_; lean_object* v___f_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; 
v___x_2701_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2700_);
v_size_2702_ = lean_ctor_get(v___x_2701_, 2);
lean_inc(v_size_2702_);
lean_dec_ref(v___x_2701_);
v___f_2703_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2703_, 0, v_size_2702_);
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2704_, 0, v_docs_2693_);
lean_closure_set(v___f_2704_, 1, v_inst_2694_);
lean_closure_set(v___f_2704_, 2, v_inst_2695_);
lean_closure_set(v___f_2704_, 3, v_deferred_2696_);
lean_closure_set(v___f_2704_, 4, v_inst_2697_);
lean_closure_set(v___f_2704_, 5, v___f_2703_);
v___x_2705_ = lean_apply_4(v_toBind_2698_, lean_box(0), lean_box(0), v_getEnv_2699_, v___f_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_toBind_2711_, lean_object* v_getEnv_2712_, lean_object* v___f_2713_, lean_object* v_____do__lift_2714_){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = l_Lean_getMainModuleDoc(v_____do__lift_2714_);
v___x_2716_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2715_);
lean_dec_ref(v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec(v___f_2713_);
lean_dec(v_getEnv_2712_);
lean_dec(v_toBind_2711_);
v___x_2717_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2718_ = l_Lean_throwError___redArg(v_inst_2709_, v_inst_2710_, v___x_2717_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; 
lean_dec_ref(v_inst_2710_);
lean_dec_ref(v_inst_2709_);
v___x_2719_ = lean_apply_4(v_toBind_2711_, lean_box(0), lean_box(0), v_getEnv_2712_, v___f_2713_);
return v___x_2719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_docs_2723_, lean_object* v_deferred_2724_){
_start:
{
lean_object* v_toBind_2725_; lean_object* v_getEnv_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; 
v_toBind_2725_ = lean_ctor_get(v_inst_2720_, 1);
lean_inc_n(v_toBind_2725_, 3);
v_getEnv_2726_ = lean_ctor_get(v_inst_2721_, 0);
lean_inc_n(v_getEnv_2726_, 3);
lean_inc_ref(v_inst_2722_);
lean_inc_ref(v_inst_2720_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2727_, 0, v_docs_2723_);
lean_closure_set(v___f_2727_, 1, v_inst_2720_);
lean_closure_set(v___f_2727_, 2, v_inst_2722_);
lean_closure_set(v___f_2727_, 3, v_deferred_2724_);
lean_closure_set(v___f_2727_, 4, v_inst_2721_);
lean_closure_set(v___f_2727_, 5, v_toBind_2725_);
lean_closure_set(v___f_2727_, 6, v_getEnv_2726_);
v___f_2728_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2728_, 0, v_inst_2720_);
lean_closure_set(v___f_2728_, 1, v_inst_2722_);
lean_closure_set(v___f_2728_, 2, v_toBind_2725_);
lean_closure_set(v___f_2728_, 3, v_getEnv_2726_);
lean_closure_set(v___f_2728_, 4, v___f_2727_);
v___x_2729_ = lean_apply_4(v_toBind_2725_, lean_box(0), lean_box(0), v_getEnv_2726_, v___f_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_docs_2735_, lean_object* v_deferred_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2731_, v_inst_2732_, v_inst_2734_, v_docs_2735_, v_deferred_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_docs_2743_, lean_object* v_deferred_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_addVersoModDocStringCore(v_m_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_docs_2743_, v_deferred_2744_);
lean_dec(v_inst_2741_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2746_, lean_object* v_as_2747_, size_t v_i_2748_, size_t v_stop_2749_, lean_object* v_b_2750_){
_start:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_usize_dec_eq(v_i_2748_, v_stop_2749_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v_index_2753_; lean_object* v_sourceString_2754_; lean_object* v_imports_2755_; lean_object* v_currNamespace_2756_; lean_object* v_openDecls_2757_; lean_object* v_options_2758_; lean_object* v_check_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2775_; 
v___x_2752_ = lean_array_uget(v_as_2747_, v_i_2748_);
v_index_2753_ = lean_ctor_get(v___x_2752_, 1);
v_sourceString_2754_ = lean_ctor_get(v___x_2752_, 2);
v_imports_2755_ = lean_ctor_get(v___x_2752_, 3);
v_currNamespace_2756_ = lean_ctor_get(v___x_2752_, 4);
v_openDecls_2757_ = lean_ctor_get(v___x_2752_, 5);
v_options_2758_ = lean_ctor_get(v___x_2752_, 6);
v_check_2759_ = lean_ctor_get(v___x_2752_, 7);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v___x_2752_, 0);
lean_dec(v_unused_2776_);
v___x_2761_ = v___x_2752_;
v_isShared_2762_ = v_isSharedCheck_2775_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_check_2759_);
lean_inc(v_options_2758_);
lean_inc(v_openDecls_2757_);
lean_inc(v_currNamespace_2756_);
lean_inc(v_imports_2755_);
lean_inc(v_sourceString_2754_);
lean_inc(v_index_2753_);
lean_dec(v___x_2752_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2775_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v_toEnvExtension_2764_; lean_object* v_asyncMode_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2763_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2764_ = lean_ctor_get(v___x_2763_, 0);
v_asyncMode_2765_ = lean_ctor_get(v_toEnvExtension_2764_, 2);
lean_inc(v_declName_2746_);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_declName_2746_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2766_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_index_2753_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_sourceString_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v_imports_2755_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v_currNamespace_2756_);
lean_ctor_set(v_reuseFailAlloc_2774_, 5, v_openDecls_2757_);
lean_ctor_set(v_reuseFailAlloc_2774_, 6, v_options_2758_);
lean_ctor_set(v_reuseFailAlloc_2774_, 7, v_check_2759_);
v___x_2768_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; size_t v___x_2771_; size_t v___x_2772_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2763_, v_b_2750_, v___x_2768_, v_asyncMode_2765_, v___x_2769_);
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_add(v_i_2748_, v___x_2771_);
v_i_2748_ = v___x_2772_;
v_b_2750_ = v___x_2770_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2746_);
return v_b_2750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2777_, lean_object* v_as_2778_, lean_object* v_i_2779_, lean_object* v_stop_2780_, lean_object* v_b_2781_){
_start:
{
size_t v_i_boxed_2782_; size_t v_stop_boxed_2783_; lean_object* v_res_2784_; 
v_i_boxed_2782_ = lean_unbox_usize(v_i_2779_);
lean_dec(v_i_2779_);
v_stop_boxed_2783_ = lean_unbox_usize(v_stop_2780_);
lean_dec(v_stop_2780_);
v_res_2784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2777_, v_as_2778_, v_i_boxed_2782_, v_stop_boxed_2783_, v_b_2781_);
lean_dec_ref(v_as_2778_);
return v_res_2784_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2791_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_ctor_set(v___x_2791_, 2, v___x_2790_);
lean_ctor_set(v___x_2791_, 3, v___x_2790_);
lean_ctor_set(v___x_2791_, 4, v___x_2790_);
lean_ctor_set(v___x_2791_, 5, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2792_, lean_object* v_docs_2793_, lean_object* v_deferred_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2834_; lean_object* v___y_2835_; uint8_t v___x_2853_; 
v___x_2853_ = l_Lean_Name_isAnonymous(v_declName_2792_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v_env_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_st_ref_get(v___y_2800_);
v_env_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_ref(v_env_2855_);
lean_dec(v___x_2854_);
v___x_2856_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2855_, v_declName_2792_);
lean_dec_ref(v_env_2855_);
if (lean_obj_tag(v___x_2856_) == 0)
{
v___y_2834_ = v___y_2798_;
v___y_2835_ = v___y_2800_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2871_; 
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; 
v_unused_2872_ = lean_ctor_get(v___x_2856_, 0);
lean_dec(v_unused_2872_);
v___x_2858_ = v___x_2856_;
v_isShared_2859_ = v_isSharedCheck_2871_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v___x_2856_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2871_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
if (v___x_2853_ == 0)
{
lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_dec_ref(v_docs_2793_);
v___x_2860_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2861_ = 1;
v___x_2862_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2792_, v___x_2861_);
v___x_2863_ = lean_string_append(v___x_2860_, v___x_2862_);
lean_dec_ref(v___x_2862_);
v___x_2864_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2865_ = lean_string_append(v___x_2863_, v___x_2864_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set_tag(v___x_2858_, 3);
lean_ctor_set(v___x_2858_, 0, v___x_2865_);
v___x_2867_ = v___x_2858_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = l_Lean_MessageData_ofFormat(v___x_2867_);
v___x_2869_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2868_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2869_;
}
}
else
{
lean_del_object(v___x_2858_);
v___y_2834_ = v___y_2798_;
v___y_2835_ = v___y_2800_;
goto v___jp_2833_;
}
}
}
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref(v_docs_2793_);
lean_dec(v_declName_2792_);
v___x_2873_ = lean_box(0);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
v___jp_2802_:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v_mctx_2817_; lean_object* v_zetaDeltaFVarIds_2818_; lean_object* v_postponed_2819_; lean_object* v_diag_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2831_; 
v___x_2813_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2814_, 0, v___y_2812_);
lean_ctor_set(v___x_2814_, 1, v___y_2805_);
lean_ctor_set(v___x_2814_, 2, v___y_2809_);
lean_ctor_set(v___x_2814_, 3, v___y_2807_);
lean_ctor_set(v___x_2814_, 4, v___y_2811_);
lean_ctor_set(v___x_2814_, 5, v___x_2813_);
lean_ctor_set(v___x_2814_, 6, v___y_2810_);
lean_ctor_set(v___x_2814_, 7, v___y_2804_);
lean_ctor_set(v___x_2814_, 8, v___y_2808_);
v___x_2815_ = lean_st_ref_put(v___y_2803_, v___x_2814_);
v___x_2816_ = lean_st_ref_take(v___y_2806_);
v_mctx_2817_ = lean_ctor_get(v___x_2816_, 0);
v_zetaDeltaFVarIds_2818_ = lean_ctor_get(v___x_2816_, 2);
v_postponed_2819_ = lean_ctor_get(v___x_2816_, 3);
v_diag_2820_ = lean_ctor_get(v___x_2816_, 4);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v___x_2816_, 1);
lean_dec(v_unused_2832_);
v___x_2822_ = v___x_2816_;
v_isShared_2823_ = v_isSharedCheck_2831_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_diag_2820_);
lean_inc(v_postponed_2819_);
lean_inc(v_zetaDeltaFVarIds_2818_);
lean_inc(v_mctx_2817_);
lean_dec(v___x_2816_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2831_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2824_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v___x_2824_);
v___x_2826_ = v___x_2822_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_mctx_2817_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v___x_2824_);
lean_ctor_set(v_reuseFailAlloc_2830_, 2, v_zetaDeltaFVarIds_2818_);
lean_ctor_set(v_reuseFailAlloc_2830_, 3, v_postponed_2819_);
lean_ctor_set(v_reuseFailAlloc_2830_, 4, v_diag_2820_);
v___x_2826_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = lean_st_ref_put(v___y_2806_, v___x_2826_);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
return v___x_2829_;
}
}
}
v___jp_2833_:
{
lean_object* v___x_2836_; lean_object* v_env_2837_; lean_object* v_nextMacroScope_2838_; lean_object* v_ngen_2839_; lean_object* v_auxDeclNGen_2840_; lean_object* v_traceState_2841_; lean_object* v_messages_2842_; lean_object* v_infoState_2843_; lean_object* v_snapshotTasks_2844_; lean_object* v___x_2845_; lean_object* v_env_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2836_ = lean_st_ref_take(v___y_2835_);
v_env_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc_ref(v_env_2837_);
v_nextMacroScope_2838_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_nextMacroScope_2838_);
v_ngen_2839_ = lean_ctor_get(v___x_2836_, 2);
lean_inc_ref(v_ngen_2839_);
v_auxDeclNGen_2840_ = lean_ctor_get(v___x_2836_, 3);
lean_inc_ref(v_auxDeclNGen_2840_);
v_traceState_2841_ = lean_ctor_get(v___x_2836_, 4);
lean_inc_ref(v_traceState_2841_);
v_messages_2842_ = lean_ctor_get(v___x_2836_, 6);
lean_inc_ref(v_messages_2842_);
v_infoState_2843_ = lean_ctor_get(v___x_2836_, 7);
lean_inc_ref(v_infoState_2843_);
v_snapshotTasks_2844_ = lean_ctor_get(v___x_2836_, 8);
lean_inc_ref(v_snapshotTasks_2844_);
lean_dec(v___x_2836_);
v___x_2845_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2792_);
v_env_2846_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2845_, v_env_2837_, v_declName_2792_, v_docs_2793_);
v___x_2847_ = lean_unsigned_to_nat(0u);
v___x_2848_ = lean_array_get_size(v_deferred_2794_);
v___x_2849_ = lean_nat_dec_lt(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_dec(v_declName_2792_);
v___y_2803_ = v___y_2835_;
v___y_2804_ = v_infoState_2843_;
v___y_2805_ = v_nextMacroScope_2838_;
v___y_2806_ = v___y_2834_;
v___y_2807_ = v_auxDeclNGen_2840_;
v___y_2808_ = v_snapshotTasks_2844_;
v___y_2809_ = v_ngen_2839_;
v___y_2810_ = v_messages_2842_;
v___y_2811_ = v_traceState_2841_;
v___y_2812_ = v_env_2846_;
goto v___jp_2802_;
}
else
{
size_t v___x_2850_; size_t v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = ((size_t)0ULL);
v___x_2851_ = lean_usize_of_nat(v___x_2848_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2792_, v_deferred_2794_, v___x_2850_, v___x_2851_, v_env_2846_);
v___y_2803_ = v___y_2835_;
v___y_2804_ = v_infoState_2843_;
v___y_2805_ = v_nextMacroScope_2838_;
v___y_2806_ = v___y_2834_;
v___y_2807_ = v_auxDeclNGen_2840_;
v___y_2808_ = v_snapshotTasks_2844_;
v___y_2809_ = v_ngen_2839_;
v___y_2810_ = v_messages_2842_;
v___y_2811_ = v_traceState_2841_;
v___y_2812_ = v___x_2852_;
goto v___jp_2802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2875_, lean_object* v_docs_2876_, lean_object* v_deferred_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2875_, v_docs_2876_, v_deferred_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v_deferred_2877_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2886_, lean_object* v_binders_2887_, lean_object* v_docComment_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___x_2916_; lean_object* v_env_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_st_ref_get(v_a_2894_);
v_env_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc_ref(v_env_2917_);
lean_dec(v___x_2916_);
v___x_2918_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2917_, v_declName_2886_);
lean_dec_ref(v_env_2917_);
if (lean_obj_tag(v___x_2918_) == 0)
{
v___y_2897_ = v_a_2889_;
v___y_2898_ = v_a_2890_;
v___y_2899_ = v_a_2891_;
v___y_2900_ = v_a_2892_;
v___y_2901_ = v_a_2893_;
v___y_2902_ = v_a_2894_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_docComment_2888_);
lean_dec(v_binders_2887_);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; 
v_unused_2934_ = lean_ctor_get(v___x_2918_, 0);
lean_dec(v_unused_2934_);
v___x_2920_ = v___x_2918_;
v_isShared_2921_ = v_isSharedCheck_2933_;
goto v_resetjp_2919_;
}
else
{
lean_dec(v___x_2918_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2933_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2922_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2923_ = 1;
v___x_2924_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2886_, v___x_2923_);
v___x_2925_ = lean_string_append(v___x_2922_, v___x_2924_);
lean_dec_ref(v___x_2924_);
v___x_2926_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2927_ = lean_string_append(v___x_2925_, v___x_2926_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set_tag(v___x_2920_, 3);
lean_ctor_set(v___x_2920_, 0, v___x_2927_);
v___x_2929_ = v___x_2920_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = l_Lean_MessageData_ofFormat(v___x_2929_);
v___x_2931_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2930_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
return v___x_2931_;
}
}
}
v___jp_2896_:
{
lean_object* v___x_2903_; 
lean_inc(v_declName_2886_);
v___x_2903_ = l_Lean_versoDocString(v_declName_2886_, v_binders_2887_, v_docComment_2888_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v_toVersoDocString_2905_; lean_object* v_deferredChecks_2906_; lean_object* v___x_2907_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v_toVersoDocString_2905_ = lean_ctor_get(v_a_2904_, 0);
lean_inc_ref(v_toVersoDocString_2905_);
v_deferredChecks_2906_ = lean_ctor_get(v_a_2904_, 1);
lean_inc_ref(v_deferredChecks_2906_);
lean_dec(v_a_2904_);
v___x_2907_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2886_, v_toVersoDocString_2905_, v_deferredChecks_2906_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
lean_dec_ref(v_deferredChecks_2906_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec(v_declName_2886_);
v_a_2908_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2903_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2903_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2935_, lean_object* v_binders_2936_, lean_object* v_docComment_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_addVersoDocString(v_declName_2935_, v_binders_2936_, v_docComment_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2946_, lean_object* v_docComment_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___x_2975_; lean_object* v_env_2976_; lean_object* v___x_2977_; 
v___x_2975_ = lean_st_ref_get(v_a_2953_);
v_env_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_ref(v_env_2976_);
lean_dec(v___x_2975_);
v___x_2977_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2976_, v_declName_2946_);
lean_dec_ref(v_env_2976_);
if (lean_obj_tag(v___x_2977_) == 0)
{
v___y_2956_ = v_a_2948_;
v___y_2957_ = v_a_2949_;
v___y_2958_ = v_a_2950_;
v___y_2959_ = v_a_2951_;
v___y_2960_ = v_a_2952_;
v___y_2961_ = v_a_2953_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v_docComment_2947_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2977_, 0);
lean_dec(v_unused_2993_);
v___x_2979_ = v___x_2977_;
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
else
{
lean_dec(v___x_2977_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2992_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; uint8_t v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2981_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2982_ = 1;
v___x_2983_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2946_, v___x_2982_);
v___x_2984_ = lean_string_append(v___x_2981_, v___x_2983_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2986_ = lean_string_append(v___x_2984_, v___x_2985_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 3);
lean_ctor_set(v___x_2979_, 0, v___x_2986_);
v___x_2988_ = v___x_2979_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = l_Lean_MessageData_ofFormat(v___x_2988_);
v___x_2990_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2989_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
return v___x_2990_;
}
}
}
v___jp_2955_:
{
lean_object* v___x_2962_; 
lean_inc(v_declName_2946_);
v___x_2962_ = l_Lean_versoDocStringFromString(v_declName_2946_, v_docComment_2947_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v_toVersoDocString_2964_; lean_object* v_deferredChecks_2965_; lean_object* v___x_2966_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v_toVersoDocString_2964_ = lean_ctor_get(v_a_2963_, 0);
lean_inc_ref(v_toVersoDocString_2964_);
v_deferredChecks_2965_ = lean_ctor_get(v_a_2963_, 1);
lean_inc_ref(v_deferredChecks_2965_);
lean_dec(v_a_2963_);
v___x_2966_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2946_, v_toVersoDocString_2964_, v_deferredChecks_2965_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref(v_deferredChecks_2965_);
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec(v_declName_2946_);
v_a_2967_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2962_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2962_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2994_, lean_object* v_docComment_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Lean_addVersoDocStringFromString(v_declName_2994_, v_docComment_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_);
lean_dec(v_a_3001_);
lean_dec_ref(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3004_, lean_object* v_msgData_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = 2;
v___x_3012_ = 0;
v___x_3013_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_3004_, v_msgData_3005_, v___x_3011_, v___x_3012_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3014_, lean_object* v_msgData_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3014_, v_msgData_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v_ref_3014_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3022_, lean_object* v_str_3023_, lean_object* v_as_3024_, size_t v_sz_3025_, size_t v_i_3026_, lean_object* v_b_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_a_3036_; uint8_t v___x_3040_; 
v___x_3040_ = lean_usize_dec_lt(v_i_3026_, v_sz_3025_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v_b_3027_);
return v___x_3041_;
}
else
{
lean_object* v_a_3042_; lean_object* v_fst_3043_; lean_object* v_snd_3044_; lean_object* v_start_3045_; lean_object* v_stop_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3066_; 
v_a_3042_ = lean_array_uget_borrowed(v_as_3024_, v_i_3026_);
v_fst_3043_ = lean_ctor_get(v_a_3042_, 0);
lean_inc(v_fst_3043_);
v_snd_3044_ = lean_ctor_get(v_a_3042_, 1);
v_start_3045_ = lean_ctor_get(v_fst_3043_, 0);
v_stop_3046_ = lean_ctor_get(v_fst_3043_, 1);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_fst_3043_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3048_ = v_fst_3043_;
v_isShared_3049_ = v_isSharedCheck_3066_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_stop_3046_);
lean_inc(v_start_3045_);
lean_dec(v_fst_3043_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3066_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_box(0);
if (lean_obj_tag(v___y_3022_) == 1)
{
lean_object* v_val_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v_val_3051_ = lean_ctor_get(v___y_3022_, 0);
v___x_3052_ = lean_nat_add(v_val_3051_, v_start_3045_);
v___x_3053_ = lean_nat_add(v_val_3051_, v_stop_3046_);
v___x_3054_ = 0;
v___x_3055_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3055_, 0, v___x_3052_);
lean_ctor_set(v___x_3055_, 1, v___x_3053_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*2, v___x_3054_);
v___x_3056_ = lean_string_utf8_extract(v_str_3023_, v_start_3045_, v_stop_3046_);
lean_dec(v_stop_3046_);
lean_dec(v_start_3045_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set_tag(v___x_3048_, 2);
lean_ctor_set(v___x_3048_, 1, v___x_3056_);
lean_ctor_set(v___x_3048_, 0, v___x_3055_);
v___x_3058_ = v___x_3048_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_inc(v_snd_3044_);
v___x_3059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3059_, 0, v_snd_3044_);
v___x_3060_ = l_Lean_MessageData_ofFormat(v___x_3059_);
v___x_3061_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3058_, v___x_3060_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec_ref(v___x_3058_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_dec_ref_known(v___x_3061_, 1);
v_a_3036_ = v___x_3050_;
goto v___jp_3035_;
}
else
{
return v___x_3061_;
}
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_del_object(v___x_3048_);
lean_dec(v_stop_3046_);
lean_dec(v_start_3045_);
lean_inc(v_snd_3044_);
v___x_3063_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3063_, 0, v_snd_3044_);
v___x_3064_ = l_Lean_MessageData_ofFormat(v___x_3063_);
v___x_3065_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3064_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_dec_ref_known(v___x_3065_, 1);
v_a_3036_ = v___x_3050_;
goto v___jp_3035_;
}
else
{
return v___x_3065_;
}
}
}
}
v___jp_3035_:
{
size_t v___x_3037_; size_t v___x_3038_; 
v___x_3037_ = ((size_t)1ULL);
v___x_3038_ = lean_usize_add(v_i_3026_, v___x_3037_);
v_i_3026_ = v___x_3038_;
v_b_3027_ = v_a_3036_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3067_, lean_object* v_str_3068_, lean_object* v_as_3069_, lean_object* v_sz_3070_, lean_object* v_i_3071_, lean_object* v_b_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
size_t v_sz_boxed_3080_; size_t v_i_boxed_3081_; lean_object* v_res_3082_; 
v_sz_boxed_3080_ = lean_unbox_usize(v_sz_3070_);
lean_dec(v_sz_3070_);
v_i_boxed_3081_ = lean_unbox_usize(v_i_3071_);
lean_dec(v_i_3071_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3067_, v_str_3068_, v_as_3069_, v_sz_boxed_3080_, v_i_boxed_3081_, v_b_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v_as_3069_);
lean_dec_ref(v_str_3068_);
lean_dec(v___y_3067_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_str_3091_; lean_object* v___y_3093_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v_str_3091_ = l_Lean_TSyntax_getDocString(v_docstring_3083_);
v___x_3108_ = lean_unsigned_to_nat(1u);
v___x_3109_ = l_Lean_Syntax_getArg(v_docstring_3083_, v___x_3108_);
v___x_3110_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3109_);
lean_dec(v___x_3109_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_box(0);
v___y_3093_ = v___x_3111_;
goto v___jp_3092_;
}
else
{
lean_object* v_val_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; 
v_val_3112_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3112_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3113_ = 0;
v___x_3114_ = l_Lean_SourceInfo_getPos_x3f(v_val_3112_, v___x_3113_);
lean_dec(v_val_3112_);
v___y_3093_ = v___x_3114_;
goto v___jp_3092_;
}
v___jp_3092_:
{
lean_object* v___x_3094_; lean_object* v_fst_3095_; lean_object* v___x_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
lean_inc_ref(v_str_3091_);
v___x_3094_ = l_Lean_rewriteManualLinksCore(v_str_3091_);
v_fst_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_fst_3095_);
lean_dec_ref(v___x_3094_);
v___x_3096_ = lean_box(0);
v_sz_3097_ = lean_array_size(v_fst_3095_);
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3093_, v_str_3091_, v_fst_3095_, v_sz_3097_, v___x_3098_, v___x_3096_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v_fst_3095_);
lean_dec_ref(v_str_3091_);
lean_dec(v___y_3093_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v___x_3099_, 0);
lean_dec(v_unused_3107_);
v___x_3101_ = v___x_3099_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___x_3099_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3096_);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3096_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
else
{
return v___x_3099_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v_docstring_3115_);
return v_res_3123_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_val_3142_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = l_Lean_Syntax_getArg(v_stx_3127_, v___x_3149_);
switch(lean_obj_tag(v___x_3150_))
{
case 2:
{
lean_object* v_val_3151_; 
lean_dec(v_stx_3127_);
v_val_3151_ = lean_ctor_get(v___x_3150_, 1);
lean_inc_ref(v_val_3151_);
lean_dec_ref_known(v___x_3150_, 2);
v_val_3142_ = v_val_3151_;
goto v___jp_3141_;
}
case 1:
{
lean_object* v_kind_3152_; 
v_kind_3152_ = lean_ctor_get(v___x_3150_, 1);
lean_inc(v_kind_3152_);
if (lean_obj_tag(v_kind_3152_) == 1)
{
lean_object* v_pre_3153_; 
v_pre_3153_ = lean_ctor_get(v_kind_3152_, 0);
lean_inc(v_pre_3153_);
if (lean_obj_tag(v_pre_3153_) == 1)
{
lean_object* v_pre_3154_; 
v_pre_3154_ = lean_ctor_get(v_pre_3153_, 0);
lean_inc(v_pre_3154_);
if (lean_obj_tag(v_pre_3154_) == 1)
{
lean_object* v_pre_3155_; 
v_pre_3155_ = lean_ctor_get(v_pre_3154_, 0);
lean_inc(v_pre_3155_);
if (lean_obj_tag(v_pre_3155_) == 1)
{
lean_object* v_pre_3156_; 
v_pre_3156_ = lean_ctor_get(v_pre_3155_, 0);
if (lean_obj_tag(v_pre_3156_) == 0)
{
lean_object* v_str_3157_; lean_object* v_str_3158_; lean_object* v_str_3159_; lean_object* v_str_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_str_3157_ = lean_ctor_get(v_kind_3152_, 1);
lean_inc_ref(v_str_3157_);
lean_dec_ref_known(v_kind_3152_, 2);
v_str_3158_ = lean_ctor_get(v_pre_3153_, 1);
lean_inc_ref(v_str_3158_);
lean_dec_ref_known(v_pre_3153_, 2);
v_str_3159_ = lean_ctor_get(v_pre_3154_, 1);
lean_inc_ref(v_str_3159_);
lean_dec_ref_known(v_pre_3154_, 2);
v_str_3160_ = lean_ctor_get(v_pre_3155_, 1);
lean_inc_ref(v_str_3160_);
lean_dec_ref_known(v_pre_3155_, 2);
v___x_3161_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3162_ = lean_string_dec_eq(v_str_3160_, v___x_3161_);
lean_dec_ref(v_str_3160_);
if (v___x_3162_ == 0)
{
lean_dec_ref(v_str_3159_);
lean_dec_ref(v_str_3158_);
lean_dec_ref(v_str_3157_);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3164_ = lean_string_dec_eq(v_str_3159_, v___x_3163_);
lean_dec_ref(v_str_3159_);
if (v___x_3164_ == 0)
{
lean_dec_ref(v_str_3158_);
lean_dec_ref(v_str_3157_);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
else
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3166_ = lean_string_dec_eq(v_str_3158_, v___x_3165_);
lean_dec_ref(v_str_3158_);
if (v___x_3166_ == 0)
{
lean_dec_ref(v_str_3157_);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
else
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3168_ = lean_string_dec_eq(v_str_3157_, v___x_3167_);
lean_dec_ref(v_str_3157_);
if (v___x_3168_ == 0)
{
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_unsigned_to_nat(0u);
v___x_3170_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_3169_);
lean_dec_ref_known(v___x_3150_, 3);
if (lean_obj_tag(v___x_3170_) == 2)
{
lean_object* v_val_3171_; 
lean_dec(v_stx_3127_);
v_val_3171_ = lean_ctor_get(v___x_3170_, 1);
lean_inc_ref(v_val_3171_);
lean_dec_ref_known(v___x_3170_, 2);
v_val_3142_ = v_val_3171_;
goto v___jp_3141_;
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec(v___x_3170_);
v___x_3172_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3127_);
v___x_3173_ = l_Lean_MessageData_ofSyntax(v_stx_3127_);
v___x_3174_ = l_Lean_indentD(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3172_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3127_, v___x_3175_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v_stx_3127_);
return v___x_3176_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3155_, 2);
lean_dec_ref_known(v_pre_3154_, 2);
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec_ref_known(v_kind_3152_, 2);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
}
else
{
lean_dec(v_pre_3155_);
lean_dec_ref_known(v_pre_3154_, 2);
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec_ref_known(v_kind_3152_, 2);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
}
else
{
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec(v_pre_3154_);
lean_dec_ref_known(v_kind_3152_, 2);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
}
else
{
lean_dec_ref_known(v_kind_3152_, 2);
lean_dec(v_pre_3153_);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
}
else
{
lean_dec(v_kind_3152_);
lean_dec_ref_known(v___x_3150_, 3);
goto v___jp_3135_;
}
}
default: 
{
lean_dec(v___x_3150_);
goto v___jp_3135_;
}
}
v___jp_3135_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3136_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3127_);
v___x_3137_ = l_Lean_MessageData_ofSyntax(v_stx_3127_);
v___x_3138_ = l_Lean_indentD(v___x_3137_);
v___x_3139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3136_);
lean_ctor_set(v___x_3139_, 1, v___x_3138_);
v___x_3140_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3127_, v___x_3139_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
lean_dec(v_stx_3127_);
return v___x_3140_;
}
v___jp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = lean_string_utf8_byte_size(v_val_3142_);
v___x_3145_ = lean_unsigned_to_nat(2u);
v___x_3146_ = lean_nat_sub(v___x_3144_, v___x_3145_);
v___x_3147_ = lean_string_utf8_extract(v_val_3142_, v___x_3143_, v___x_3146_);
lean_dec(v___x_3146_);
lean_dec_ref(v_val_3142_);
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3186_, lean_object* v_docComment_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; uint8_t v___x_3258_; 
v___x_3258_ = l_Lean_Name_isAnonymous(v_declName_3186_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v_env_3260_; lean_object* v___x_3261_; 
v___x_3259_ = lean_st_ref_get(v___y_3193_);
v_env_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_env_3260_);
lean_dec(v___x_3259_);
v___x_3261_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3260_, v_declName_3186_);
lean_dec_ref(v_env_3260_);
if (lean_obj_tag(v___x_3261_) == 0)
{
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
v___y_3200_ = v___y_3192_;
v___y_3201_ = v___y_3193_;
goto v___jp_3195_;
}
else
{
lean_dec_ref_known(v___x_3261_, 1);
if (v___x_3258_ == 0)
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec(v_docComment_3187_);
v___x_3262_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3263_ = l_Lean_MessageData_ofConstName(v_declName_3186_, v___x_3258_);
v___x_3264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3266_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
return v___x_3267_;
}
else
{
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
v___y_3200_ = v___y_3192_;
v___y_3201_ = v___y_3193_;
goto v___jp_3195_;
}
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec(v_docComment_3187_);
lean_dec(v_declName_3186_);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3268_);
return v___x_3269_;
}
v___jp_3195_:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3187_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref_known(v___x_3202_, 1);
v___x_3203_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3187_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3249_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3249_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3249_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v_env_3209_; lean_object* v_nextMacroScope_3210_; lean_object* v_ngen_3211_; lean_object* v_auxDeclNGen_3212_; lean_object* v_traceState_3213_; lean_object* v_messages_3214_; lean_object* v_infoState_3215_; lean_object* v_snapshotTasks_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3247_; 
v___x_3208_ = lean_st_ref_take(v___y_3201_);
v_env_3209_ = lean_ctor_get(v___x_3208_, 0);
v_nextMacroScope_3210_ = lean_ctor_get(v___x_3208_, 1);
v_ngen_3211_ = lean_ctor_get(v___x_3208_, 2);
v_auxDeclNGen_3212_ = lean_ctor_get(v___x_3208_, 3);
v_traceState_3213_ = lean_ctor_get(v___x_3208_, 4);
v_messages_3214_ = lean_ctor_get(v___x_3208_, 6);
v_infoState_3215_ = lean_ctor_get(v___x_3208_, 7);
v_snapshotTasks_3216_ = lean_ctor_get(v___x_3208_, 8);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3208_, 5);
lean_dec(v_unused_3248_);
v___x_3218_ = v___x_3208_;
v_isShared_3219_ = v_isSharedCheck_3247_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_snapshotTasks_3216_);
lean_inc(v_infoState_3215_);
lean_inc(v_messages_3214_);
lean_inc(v_traceState_3213_);
lean_inc(v_auxDeclNGen_3212_);
lean_inc(v_ngen_3211_);
lean_inc(v_nextMacroScope_3210_);
lean_inc(v_env_3209_);
lean_dec(v___x_3208_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3247_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3220_ = l_Lean_docStringExt;
v___x_3221_ = l_String_removeLeadingSpaces(v_a_3204_);
v___x_3222_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3220_, v_env_3209_, v_declName_3186_, v___x_3221_);
v___x_3223_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 5, v___x_3223_);
lean_ctor_set(v___x_3218_, 0, v___x_3222_);
v___x_3225_ = v___x_3218_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_nextMacroScope_3210_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_ngen_3211_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_auxDeclNGen_3212_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_traceState_3213_);
lean_ctor_set(v_reuseFailAlloc_3246_, 5, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3246_, 6, v_messages_3214_);
lean_ctor_set(v_reuseFailAlloc_3246_, 7, v_infoState_3215_);
lean_ctor_set(v_reuseFailAlloc_3246_, 8, v_snapshotTasks_3216_);
v___x_3225_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_mctx_3228_; lean_object* v_zetaDeltaFVarIds_3229_; lean_object* v_postponed_3230_; lean_object* v_diag_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3244_; 
v___x_3226_ = lean_st_ref_put(v___y_3201_, v___x_3225_);
v___x_3227_ = lean_st_ref_take(v___y_3199_);
v_mctx_3228_ = lean_ctor_get(v___x_3227_, 0);
v_zetaDeltaFVarIds_3229_ = lean_ctor_get(v___x_3227_, 2);
v_postponed_3230_ = lean_ctor_get(v___x_3227_, 3);
v_diag_3231_ = lean_ctor_get(v___x_3227_, 4);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v___x_3227_, 1);
lean_dec(v_unused_3245_);
v___x_3233_ = v___x_3227_;
v_isShared_3234_ = v_isSharedCheck_3244_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_diag_3231_);
lean_inc(v_postponed_3230_);
lean_inc(v_zetaDeltaFVarIds_3229_);
lean_inc(v_mctx_3228_);
lean_dec(v___x_3227_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3244_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3235_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3235_);
v___x_3237_ = v___x_3233_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_mctx_3228_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_zetaDeltaFVarIds_3229_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_postponed_3230_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v_diag_3231_);
v___x_3237_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3238_ = lean_st_ref_put(v___y_3199_, v___x_3237_);
v___x_3239_ = lean_box(0);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3239_);
v___x_3241_ = v___x_3206_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_declName_3186_);
v_a_3250_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3203_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3203_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_dec(v_docComment_3187_);
lean_dec(v_declName_3186_);
return v___x_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3270_, lean_object* v_docComment_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3270_, v_docComment_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3280_, lean_object* v_declName_3281_, lean_object* v_binders_3282_, lean_object* v_docComment_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
if (v_isVerso_3280_ == 0)
{
lean_object* v___x_3291_; 
lean_dec(v_binders_3282_);
v___x_3291_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3281_, v_docComment_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; 
v___x_3292_ = l_Lean_addVersoDocString(v_declName_3281_, v_binders_3282_, v_docComment_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3293_, lean_object* v_declName_3294_, lean_object* v_binders_3295_, lean_object* v_docComment_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_){
_start:
{
uint8_t v_isVerso_boxed_3304_; lean_object* v_res_3305_; 
v_isVerso_boxed_3304_ = lean_unbox(v_isVerso_3293_);
v_res_3305_ = l_Lean_addDocStringOf(v_isVerso_boxed_3304_, v_declName_3294_, v_binders_3295_, v_docComment_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3306_, lean_object* v_msgData_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
v___x_3315_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3306_, v_msgData_3307_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3316_, lean_object* v_msgData_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3316_, v_msgData_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v_ref_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3326_, lean_object* v_t_3327_){
_start:
{
if (lean_obj_tag(v_t_3327_) == 0)
{
lean_object* v_k_3328_; lean_object* v_v_3329_; lean_object* v_l_3330_; lean_object* v_r_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3985_; 
v_k_3328_ = lean_ctor_get(v_t_3327_, 1);
v_v_3329_ = lean_ctor_get(v_t_3327_, 2);
v_l_3330_ = lean_ctor_get(v_t_3327_, 3);
v_r_3331_ = lean_ctor_get(v_t_3327_, 4);
v_isSharedCheck_3985_ = !lean_is_exclusive(v_t_3327_);
if (v_isSharedCheck_3985_ == 0)
{
lean_object* v_unused_3986_; 
v_unused_3986_ = lean_ctor_get(v_t_3327_, 0);
lean_dec(v_unused_3986_);
v___x_3333_ = v_t_3327_;
v_isShared_3334_ = v_isSharedCheck_3985_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_r_3331_);
lean_inc(v_l_3330_);
lean_inc(v_v_3329_);
lean_inc(v_k_3328_);
lean_dec(v_t_3327_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3985_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
uint8_t v___x_3335_; 
v___x_3335_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3326_, v_k_3328_);
switch(v___x_3335_)
{
case 0:
{
lean_object* v_impl_3336_; lean_object* v___x_3337_; 
v_impl_3336_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3326_, v_l_3330_);
v___x_3337_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3336_) == 0)
{
if (lean_obj_tag(v_r_3331_) == 0)
{
lean_object* v_size_3338_; lean_object* v_size_3339_; lean_object* v_k_3340_; lean_object* v_v_3341_; lean_object* v_l_3342_; lean_object* v_r_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_size_3338_ = lean_ctor_get(v_impl_3336_, 0);
lean_inc(v_size_3338_);
v_size_3339_ = lean_ctor_get(v_r_3331_, 0);
v_k_3340_ = lean_ctor_get(v_r_3331_, 1);
v_v_3341_ = lean_ctor_get(v_r_3331_, 2);
v_l_3342_ = lean_ctor_get(v_r_3331_, 3);
lean_inc(v_l_3342_);
v_r_3343_ = lean_ctor_get(v_r_3331_, 4);
v___x_3344_ = lean_unsigned_to_nat(3u);
v___x_3345_ = lean_nat_mul(v___x_3344_, v_size_3338_);
v___x_3346_ = lean_nat_dec_lt(v___x_3345_, v_size_3339_);
lean_dec(v___x_3345_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
lean_dec(v_l_3342_);
v___x_3347_ = lean_nat_add(v___x_3337_, v_size_3338_);
lean_dec(v_size_3338_);
v___x_3348_ = lean_nat_add(v___x_3347_, v_size_3339_);
lean_dec(v___x_3347_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 3, v_impl_3336_);
lean_ctor_set(v___x_3333_, 0, v___x_3348_);
v___x_3350_ = v___x_3333_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_impl_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 4, v_r_3331_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
else
{
lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3415_; 
lean_inc(v_r_3343_);
lean_inc(v_v_3341_);
lean_inc(v_k_3340_);
lean_inc(v_size_3339_);
v_isSharedCheck_3415_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; lean_object* v_unused_3420_; 
v_unused_3416_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3416_);
v_unused_3417_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_r_3331_, 2);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_r_3331_, 1);
lean_dec(v_unused_3419_);
v_unused_3420_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3420_);
v___x_3353_ = v_r_3331_;
v_isShared_3354_ = v_isSharedCheck_3415_;
goto v_resetjp_3352_;
}
else
{
lean_dec(v_r_3331_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3415_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v_size_3355_; lean_object* v_k_3356_; lean_object* v_v_3357_; lean_object* v_l_3358_; lean_object* v_r_3359_; lean_object* v_size_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_size_3355_ = lean_ctor_get(v_l_3342_, 0);
v_k_3356_ = lean_ctor_get(v_l_3342_, 1);
v_v_3357_ = lean_ctor_get(v_l_3342_, 2);
v_l_3358_ = lean_ctor_get(v_l_3342_, 3);
v_r_3359_ = lean_ctor_get(v_l_3342_, 4);
v_size_3360_ = lean_ctor_get(v_r_3343_, 0);
v___x_3361_ = lean_unsigned_to_nat(2u);
v___x_3362_ = lean_nat_mul(v___x_3361_, v_size_3360_);
v___x_3363_ = lean_nat_dec_lt(v_size_3355_, v___x_3362_);
lean_dec(v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3391_; 
lean_inc(v_r_3359_);
lean_inc(v_l_3358_);
lean_inc(v_v_3357_);
lean_inc(v_k_3356_);
v_isSharedCheck_3391_ = !lean_is_exclusive(v_l_3342_);
if (v_isSharedCheck_3391_ == 0)
{
lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; lean_object* v_unused_3396_; 
v_unused_3392_ = lean_ctor_get(v_l_3342_, 4);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_l_3342_, 3);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_l_3342_, 2);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_l_3342_, 1);
lean_dec(v_unused_3395_);
v_unused_3396_ = lean_ctor_get(v_l_3342_, 0);
lean_dec(v_unused_3396_);
v___x_3365_ = v_l_3342_;
v_isShared_3366_ = v_isSharedCheck_3391_;
goto v_resetjp_3364_;
}
else
{
lean_dec(v_l_3342_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3391_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3381_; 
v___x_3367_ = lean_nat_add(v___x_3337_, v_size_3338_);
lean_dec(v_size_3338_);
v___x_3368_ = lean_nat_add(v___x_3367_, v_size_3339_);
lean_dec(v_size_3339_);
if (lean_obj_tag(v_l_3358_) == 0)
{
lean_object* v_size_3389_; 
v_size_3389_ = lean_ctor_get(v_l_3358_, 0);
lean_inc(v_size_3389_);
v___y_3381_ = v_size_3389_;
goto v___jp_3380_;
}
else
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_unsigned_to_nat(0u);
v___y_3381_ = v___x_3390_;
goto v___jp_3380_;
}
v___jp_3369_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_nat_add(v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec(v___y_3371_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 4, v_r_3343_);
lean_ctor_set(v___x_3365_, 3, v_r_3359_);
lean_ctor_set(v___x_3365_, 2, v_v_3341_);
lean_ctor_set(v___x_3365_, 1, v_k_3340_);
lean_ctor_set(v___x_3365_, 0, v___x_3373_);
v___x_3375_ = v___x_3365_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3340_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3341_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_r_3359_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_r_3343_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v___x_3375_);
lean_ctor_set(v___x_3353_, 3, v___y_3370_);
lean_ctor_set(v___x_3353_, 2, v_v_3357_);
lean_ctor_set(v___x_3353_, 1, v_k_3356_);
lean_ctor_set(v___x_3353_, 0, v___x_3368_);
v___x_3377_ = v___x_3353_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3356_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3357_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v___y_3370_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
v___jp_3380_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = lean_nat_add(v___x_3367_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec(v___x_3367_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_l_3358_);
lean_ctor_set(v___x_3333_, 3, v_impl_3336_);
lean_ctor_set(v___x_3333_, 0, v___x_3382_);
v___x_3384_ = v___x_3333_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_impl_3336_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v_l_3358_);
v___x_3384_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_nat_add(v___x_3337_, v_size_3360_);
if (lean_obj_tag(v_r_3359_) == 0)
{
lean_object* v_size_3386_; 
v_size_3386_ = lean_ctor_get(v_r_3359_, 0);
lean_inc(v_size_3386_);
v___y_3370_ = v___x_3384_;
v___y_3371_ = v___x_3385_;
v___y_3372_ = v_size_3386_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3387_; 
v___x_3387_ = lean_unsigned_to_nat(0u);
v___y_3370_ = v___x_3384_;
v___y_3371_ = v___x_3385_;
v___y_3372_ = v___x_3387_;
goto v___jp_3369_;
}
}
}
}
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3401_; 
lean_del_object(v___x_3333_);
v___x_3397_ = lean_nat_add(v___x_3337_, v_size_3338_);
lean_dec(v_size_3338_);
v___x_3398_ = lean_nat_add(v___x_3397_, v_size_3339_);
lean_dec(v_size_3339_);
v___x_3399_ = lean_nat_add(v___x_3397_, v_size_3355_);
lean_dec(v___x_3397_);
lean_inc_ref(v_impl_3336_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_l_3342_);
lean_ctor_set(v___x_3353_, 3, v_impl_3336_);
lean_ctor_set(v___x_3353_, 2, v_v_3329_);
lean_ctor_set(v___x_3353_, 1, v_k_3328_);
lean_ctor_set(v___x_3353_, 0, v___x_3399_);
v___x_3401_ = v___x_3353_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_impl_3336_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_l_3342_);
v___x_3401_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
v_isSharedCheck_3408_ = !lean_is_exclusive(v_impl_3336_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; lean_object* v_unused_3413_; 
v_unused_3409_ = lean_ctor_get(v_impl_3336_, 4);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_impl_3336_, 3);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_impl_3336_, 2);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_impl_3336_, 1);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_impl_3336_, 0);
lean_dec(v_unused_3413_);
v___x_3403_ = v_impl_3336_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v_impl_3336_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 4, v_r_3343_);
lean_ctor_set(v___x_3403_, 3, v___x_3401_);
lean_ctor_set(v___x_3403_, 2, v_v_3341_);
lean_ctor_set(v___x_3403_, 1, v_k_3340_);
lean_ctor_set(v___x_3403_, 0, v___x_3398_);
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_k_3340_);
lean_ctor_set(v_reuseFailAlloc_3407_, 2, v_v_3341_);
lean_ctor_set(v_reuseFailAlloc_3407_, 3, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3407_, 4, v_r_3343_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v_size_3421_ = lean_ctor_get(v_impl_3336_, 0);
lean_inc(v_size_3421_);
v___x_3422_ = lean_nat_add(v___x_3337_, v_size_3421_);
lean_dec(v_size_3421_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 3, v_impl_3336_);
lean_ctor_set(v___x_3333_, 0, v___x_3422_);
v___x_3424_ = v___x_3333_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3425_, 3, v_impl_3336_);
lean_ctor_set(v_reuseFailAlloc_3425_, 4, v_r_3331_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
else
{
if (lean_obj_tag(v_r_3331_) == 0)
{
lean_object* v_l_3426_; 
v_l_3426_ = lean_ctor_get(v_r_3331_, 3);
lean_inc(v_l_3426_);
if (lean_obj_tag(v_l_3426_) == 0)
{
lean_object* v_r_3427_; 
v_r_3427_ = lean_ctor_get(v_r_3331_, 4);
lean_inc(v_r_3427_);
if (lean_obj_tag(v_r_3427_) == 0)
{
lean_object* v_size_3428_; lean_object* v_k_3429_; lean_object* v_v_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3443_; 
v_size_3428_ = lean_ctor_get(v_r_3331_, 0);
v_k_3429_ = lean_ctor_get(v_r_3331_, 1);
v_v_3430_ = lean_ctor_get(v_r_3331_, 2);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; lean_object* v_unused_3445_; 
v_unused_3444_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3444_);
v_unused_3445_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3445_);
v___x_3432_ = v_r_3331_;
v_isShared_3433_ = v_isSharedCheck_3443_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_v_3430_);
lean_inc(v_k_3429_);
lean_inc(v_size_3428_);
lean_dec(v_r_3331_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3443_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_size_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v_size_3434_ = lean_ctor_get(v_l_3426_, 0);
v___x_3435_ = lean_nat_add(v___x_3337_, v_size_3428_);
lean_dec(v_size_3428_);
v___x_3436_ = lean_nat_add(v___x_3337_, v_size_3434_);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 4, v_l_3426_);
lean_ctor_set(v___x_3432_, 3, v_impl_3336_);
lean_ctor_set(v___x_3432_, 2, v_v_3329_);
lean_ctor_set(v___x_3432_, 1, v_k_3328_);
lean_ctor_set(v___x_3432_, 0, v___x_3436_);
v___x_3438_ = v___x_3432_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3442_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3442_, 3, v_impl_3336_);
lean_ctor_set(v_reuseFailAlloc_3442_, 4, v_l_3426_);
v___x_3438_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3440_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_r_3427_);
lean_ctor_set(v___x_3333_, 3, v___x_3438_);
lean_ctor_set(v___x_3333_, 2, v_v_3430_);
lean_ctor_set(v___x_3333_, 1, v_k_3429_);
lean_ctor_set(v___x_3333_, 0, v___x_3435_);
v___x_3440_ = v___x_3333_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_k_3429_);
lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_v_3430_);
lean_ctor_set(v_reuseFailAlloc_3441_, 3, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3441_, 4, v_r_3427_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v_k_3446_; lean_object* v_v_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3470_; 
v_k_3446_ = lean_ctor_get(v_r_3331_, 1);
v_v_3447_ = lean_ctor_get(v_r_3331_, 2);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; lean_object* v_unused_3472_; lean_object* v_unused_3473_; 
v_unused_3471_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3472_);
v_unused_3473_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3473_);
v___x_3449_ = v_r_3331_;
v_isShared_3450_ = v_isSharedCheck_3470_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_v_3447_);
lean_inc(v_k_3446_);
lean_dec(v_r_3331_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3470_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_k_3451_; lean_object* v_v_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3466_; 
v_k_3451_ = lean_ctor_get(v_l_3426_, 1);
v_v_3452_ = lean_ctor_get(v_l_3426_, 2);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_l_3426_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; 
v_unused_3467_ = lean_ctor_get(v_l_3426_, 4);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_l_3426_, 3);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_l_3426_, 0);
lean_dec(v_unused_3469_);
v___x_3454_ = v_l_3426_;
v_isShared_3455_ = v_isSharedCheck_3466_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_v_3452_);
lean_inc(v_k_3451_);
lean_dec(v_l_3426_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3466_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = lean_unsigned_to_nat(3u);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 4, v_r_3427_);
lean_ctor_set(v___x_3454_, 3, v_r_3427_);
lean_ctor_set(v___x_3454_, 2, v_v_3329_);
lean_ctor_set(v___x_3454_, 1, v_k_3328_);
lean_ctor_set(v___x_3454_, 0, v___x_3337_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_r_3427_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v_r_3427_);
v___x_3458_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 3, v_r_3427_);
lean_ctor_set(v___x_3449_, 0, v___x_3337_);
v___x_3460_ = v___x_3449_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_k_3446_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_v_3447_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_r_3427_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_r_3427_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v___x_3460_);
lean_ctor_set(v___x_3333_, 3, v___x_3458_);
lean_ctor_set(v___x_3333_, 2, v_v_3452_);
lean_ctor_set(v___x_3333_, 1, v_k_3451_);
lean_ctor_set(v___x_3333_, 0, v___x_3456_);
v___x_3462_ = v___x_3333_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3451_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3452_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3474_; 
v_r_3474_ = lean_ctor_get(v_r_3331_, 4);
lean_inc(v_r_3474_);
if (lean_obj_tag(v_r_3474_) == 0)
{
lean_object* v_k_3475_; lean_object* v_v_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3487_; 
v_k_3475_ = lean_ctor_get(v_r_3331_, 1);
v_v_3476_ = lean_ctor_get(v_r_3331_, 2);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; lean_object* v_unused_3490_; 
v_unused_3488_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3490_);
v___x_3478_ = v_r_3331_;
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_v_3476_);
lean_inc(v_k_3475_);
lean_dec(v_r_3331_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = lean_unsigned_to_nat(3u);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 4, v_l_3426_);
lean_ctor_set(v___x_3478_, 2, v_v_3329_);
lean_ctor_set(v___x_3478_, 1, v_k_3328_);
lean_ctor_set(v___x_3478_, 0, v___x_3337_);
v___x_3482_ = v___x_3478_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_l_3426_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_l_3426_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_r_3474_);
lean_ctor_set(v___x_3333_, 3, v___x_3482_);
lean_ctor_set(v___x_3333_, 2, v_v_3476_);
lean_ctor_set(v___x_3333_, 1, v_k_3475_);
lean_ctor_set(v___x_3333_, 0, v___x_3480_);
v___x_3484_ = v___x_3333_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3475_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3476_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_r_3474_);
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
else
{
lean_object* v_size_3491_; lean_object* v_k_3492_; lean_object* v_v_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3504_; 
v_size_3491_ = lean_ctor_get(v_r_3331_, 0);
v_k_3492_ = lean_ctor_get(v_r_3331_, 1);
v_v_3493_ = lean_ctor_get(v_r_3331_, 2);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3504_ == 0)
{
lean_object* v_unused_3505_; lean_object* v_unused_3506_; 
v_unused_3505_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3505_);
v_unused_3506_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3506_);
v___x_3495_ = v_r_3331_;
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_v_3493_);
lean_inc(v_k_3492_);
lean_inc(v_size_3491_);
lean_dec(v_r_3331_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 3, v_r_3474_);
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_size_3491_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_k_3492_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v_v_3493_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_r_3474_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_r_3474_);
v___x_3498_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3499_ = lean_unsigned_to_nat(2u);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v___x_3498_);
lean_ctor_set(v___x_3333_, 3, v_r_3474_);
lean_ctor_set(v___x_3333_, 0, v___x_3499_);
v___x_3501_ = v___x_3333_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_r_3474_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v___x_3498_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
else
{
lean_object* v___x_3508_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 3, v_r_3331_);
lean_ctor_set(v___x_3333_, 0, v___x_3337_);
v___x_3508_ = v___x_3333_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3337_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3509_, 3, v_r_3331_);
lean_ctor_set(v_reuseFailAlloc_3509_, 4, v_r_3331_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3333_);
lean_dec(v_v_3329_);
lean_dec(v_k_3328_);
if (lean_obj_tag(v_l_3330_) == 0)
{
if (lean_obj_tag(v_r_3331_) == 0)
{
lean_object* v_size_3510_; lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v_l_3513_; lean_object* v_r_3514_; lean_object* v_size_3515_; lean_object* v_k_3516_; lean_object* v_v_3517_; lean_object* v_l_3518_; lean_object* v_r_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v_size_3510_ = lean_ctor_get(v_l_3330_, 0);
v_k_3511_ = lean_ctor_get(v_l_3330_, 1);
v_v_3512_ = lean_ctor_get(v_l_3330_, 2);
v_l_3513_ = lean_ctor_get(v_l_3330_, 3);
v_r_3514_ = lean_ctor_get(v_l_3330_, 4);
lean_inc(v_r_3514_);
v_size_3515_ = lean_ctor_get(v_r_3331_, 0);
v_k_3516_ = lean_ctor_get(v_r_3331_, 1);
v_v_3517_ = lean_ctor_get(v_r_3331_, 2);
v_l_3518_ = lean_ctor_get(v_r_3331_, 3);
lean_inc(v_l_3518_);
v_r_3519_ = lean_ctor_get(v_r_3331_, 4);
v___x_3520_ = lean_unsigned_to_nat(1u);
v___x_3521_ = lean_nat_dec_lt(v_size_3510_, v_size_3515_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3657_; 
lean_inc(v_l_3513_);
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; lean_object* v_unused_3659_; lean_object* v_unused_3660_; lean_object* v_unused_3661_; lean_object* v_unused_3662_; 
v_unused_3658_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3659_);
v_unused_3660_ = lean_ctor_get(v_l_3330_, 2);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v_l_3330_, 1);
lean_dec(v_unused_3661_);
v_unused_3662_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3662_);
v___x_3523_ = v_l_3330_;
v_isShared_3524_ = v_isSharedCheck_3657_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_l_3330_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3657_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v_tree_3526_; 
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3511_, v_v_3512_, v_l_3513_, v_r_3514_);
v_tree_3526_ = lean_ctor_get(v___x_3525_, 2);
lean_inc(v_tree_3526_);
if (lean_obj_tag(v_tree_3526_) == 0)
{
lean_object* v_k_3527_; lean_object* v_v_3528_; lean_object* v_size_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v_k_3527_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_k_3527_);
v_v_3528_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_v_3528_);
lean_dec_ref(v___x_3525_);
v_size_3529_ = lean_ctor_get(v_tree_3526_, 0);
v___x_3530_ = lean_unsigned_to_nat(3u);
v___x_3531_ = lean_nat_mul(v___x_3530_, v_size_3529_);
v___x_3532_ = lean_nat_dec_lt(v___x_3531_, v_size_3515_);
lean_dec(v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
lean_dec(v_l_3518_);
v___x_3533_ = lean_nat_add(v___x_3520_, v_size_3529_);
v___x_3534_ = lean_nat_add(v___x_3533_, v_size_3515_);
lean_dec(v___x_3533_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_r_3331_);
lean_ctor_set(v___x_3523_, 3, v_tree_3526_);
lean_ctor_set(v___x_3523_, 2, v_v_3528_);
lean_ctor_set(v___x_3523_, 1, v_k_3527_);
lean_ctor_set(v___x_3523_, 0, v___x_3534_);
v___x_3536_ = v___x_3523_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3527_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3528_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_tree_3526_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_r_3331_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
else
{
lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3592_; 
lean_inc(v_r_3519_);
lean_inc(v_v_3517_);
lean_inc(v_k_3516_);
lean_inc(v_size_3515_);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3592_ == 0)
{
lean_object* v_unused_3593_; lean_object* v_unused_3594_; lean_object* v_unused_3595_; lean_object* v_unused_3596_; lean_object* v_unused_3597_; 
v_unused_3593_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_r_3331_, 2);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_r_3331_, 1);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3597_);
v___x_3539_ = v_r_3331_;
v_isShared_3540_ = v_isSharedCheck_3592_;
goto v_resetjp_3538_;
}
else
{
lean_dec(v_r_3331_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3592_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v_size_3541_; lean_object* v_k_3542_; lean_object* v_v_3543_; lean_object* v_l_3544_; lean_object* v_r_3545_; lean_object* v_size_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_size_3541_ = lean_ctor_get(v_l_3518_, 0);
v_k_3542_ = lean_ctor_get(v_l_3518_, 1);
v_v_3543_ = lean_ctor_get(v_l_3518_, 2);
v_l_3544_ = lean_ctor_get(v_l_3518_, 3);
v_r_3545_ = lean_ctor_get(v_l_3518_, 4);
v_size_3546_ = lean_ctor_get(v_r_3519_, 0);
v___x_3547_ = lean_unsigned_to_nat(2u);
v___x_3548_ = lean_nat_mul(v___x_3547_, v_size_3546_);
v___x_3549_ = lean_nat_dec_lt(v_size_3541_, v___x_3548_);
lean_dec(v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3577_; 
lean_inc(v_r_3545_);
lean_inc(v_l_3544_);
lean_inc(v_v_3543_);
lean_inc(v_k_3542_);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_l_3518_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3578_ = lean_ctor_get(v_l_3518_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_l_3518_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_l_3518_, 2);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_l_3518_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_l_3518_, 0);
lean_dec(v_unused_3582_);
v___x_3551_ = v_l_3518_;
v_isShared_3552_ = v_isSharedCheck_3577_;
goto v_resetjp_3550_;
}
else
{
lean_dec(v_l_3518_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3577_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3567_; 
v___x_3553_ = lean_nat_add(v___x_3520_, v_size_3529_);
v___x_3554_ = lean_nat_add(v___x_3553_, v_size_3515_);
lean_dec(v_size_3515_);
if (lean_obj_tag(v_l_3544_) == 0)
{
lean_object* v_size_3575_; 
v_size_3575_ = lean_ctor_get(v_l_3544_, 0);
lean_inc(v_size_3575_);
v___y_3567_ = v_size_3575_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_unsigned_to_nat(0u);
v___y_3567_ = v___x_3576_;
goto v___jp_3566_;
}
v___jp_3555_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_nat_add(v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec(v___y_3557_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 4, v_r_3519_);
lean_ctor_set(v___x_3551_, 3, v_r_3545_);
lean_ctor_set(v___x_3551_, 2, v_v_3517_);
lean_ctor_set(v___x_3551_, 1, v_k_3516_);
lean_ctor_set(v___x_3551_, 0, v___x_3559_);
v___x_3561_ = v___x_3551_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_r_3545_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_r_3519_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 4, v___x_3561_);
lean_ctor_set(v___x_3539_, 3, v___y_3556_);
lean_ctor_set(v___x_3539_, 2, v_v_3543_);
lean_ctor_set(v___x_3539_, 1, v_k_3542_);
lean_ctor_set(v___x_3539_, 0, v___x_3554_);
v___x_3563_ = v___x_3539_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3542_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3543_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v___y_3556_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
v___jp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_nat_add(v___x_3553_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec(v___x_3553_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_l_3544_);
lean_ctor_set(v___x_3523_, 3, v_tree_3526_);
lean_ctor_set(v___x_3523_, 2, v_v_3528_);
lean_ctor_set(v___x_3523_, 1, v_k_3527_);
lean_ctor_set(v___x_3523_, 0, v___x_3568_);
v___x_3570_ = v___x_3523_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_k_3527_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_v_3528_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_tree_3526_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_l_3544_);
v___x_3570_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_nat_add(v___x_3520_, v_size_3546_);
if (lean_obj_tag(v_r_3545_) == 0)
{
lean_object* v_size_3572_; 
v_size_3572_ = lean_ctor_get(v_r_3545_, 0);
lean_inc(v_size_3572_);
v___y_3556_ = v___x_3570_;
v___y_3557_ = v___x_3571_;
v___y_3558_ = v_size_3572_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___y_3556_ = v___x_3570_;
v___y_3557_ = v___x_3571_;
v___y_3558_ = v___x_3573_;
goto v___jp_3555_;
}
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3587_; 
v___x_3583_ = lean_nat_add(v___x_3520_, v_size_3529_);
v___x_3584_ = lean_nat_add(v___x_3583_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3585_ = lean_nat_add(v___x_3583_, v_size_3541_);
lean_dec(v___x_3583_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 4, v_l_3518_);
lean_ctor_set(v___x_3539_, 3, v_tree_3526_);
lean_ctor_set(v___x_3539_, 2, v_v_3528_);
lean_ctor_set(v___x_3539_, 1, v_k_3527_);
lean_ctor_set(v___x_3539_, 0, v___x_3585_);
v___x_3587_ = v___x_3539_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v_k_3527_);
lean_ctor_set(v_reuseFailAlloc_3591_, 2, v_v_3528_);
lean_ctor_set(v_reuseFailAlloc_3591_, 3, v_tree_3526_);
lean_ctor_set(v_reuseFailAlloc_3591_, 4, v_l_3518_);
v___x_3587_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_r_3519_);
lean_ctor_set(v___x_3523_, 3, v___x_3587_);
lean_ctor_set(v___x_3523_, 2, v_v_3517_);
lean_ctor_set(v___x_3523_, 1, v_k_3516_);
lean_ctor_set(v___x_3523_, 0, v___x_3584_);
v___x_3589_ = v___x_3523_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_r_3519_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
}
else
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3651_; 
lean_inc(v_r_3519_);
lean_inc(v_v_3517_);
lean_inc(v_k_3516_);
lean_inc(v_size_3515_);
v_isSharedCheck_3651_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3651_ == 0)
{
lean_object* v_unused_3652_; lean_object* v_unused_3653_; lean_object* v_unused_3654_; lean_object* v_unused_3655_; lean_object* v_unused_3656_; 
v_unused_3652_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_r_3331_, 2);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_r_3331_, 1);
lean_dec(v_unused_3655_);
v_unused_3656_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3656_);
v___x_3599_ = v_r_3331_;
v_isShared_3600_ = v_isSharedCheck_3651_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v_r_3331_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3651_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
if (lean_obj_tag(v_l_3518_) == 0)
{
if (lean_obj_tag(v_r_3519_) == 0)
{
lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v_size_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v_k_3601_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_k_3601_);
v_v_3602_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_v_3602_);
lean_dec_ref(v___x_3525_);
v_size_3603_ = lean_ctor_get(v_l_3518_, 0);
v___x_3604_ = lean_nat_add(v___x_3520_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3605_ = lean_nat_add(v___x_3520_, v_size_3603_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 4, v_l_3518_);
lean_ctor_set(v___x_3599_, 3, v_tree_3526_);
lean_ctor_set(v___x_3599_, 2, v_v_3602_);
lean_ctor_set(v___x_3599_, 1, v_k_3601_);
lean_ctor_set(v___x_3599_, 0, v___x_3605_);
v___x_3607_ = v___x_3599_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_tree_3526_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_l_3518_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_r_3519_);
lean_ctor_set(v___x_3523_, 3, v___x_3607_);
lean_ctor_set(v___x_3523_, 2, v_v_3517_);
lean_ctor_set(v___x_3523_, 1, v_k_3516_);
lean_ctor_set(v___x_3523_, 0, v___x_3604_);
v___x_3609_ = v___x_3523_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_r_3519_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
else
{
lean_object* v_k_3612_; lean_object* v_v_3613_; lean_object* v_k_3614_; lean_object* v_v_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_size_3515_);
v_k_3612_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_k_3612_);
v_v_3613_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_v_3613_);
lean_dec_ref(v___x_3525_);
v_k_3614_ = lean_ctor_get(v_l_3518_, 1);
v_v_3615_ = lean_ctor_get(v_l_3518_, 2);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_l_3518_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; lean_object* v_unused_3631_; lean_object* v_unused_3632_; 
v_unused_3630_ = lean_ctor_get(v_l_3518_, 4);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_l_3518_, 3);
lean_dec(v_unused_3631_);
v_unused_3632_ = lean_ctor_get(v_l_3518_, 0);
lean_dec(v_unused_3632_);
v___x_3617_ = v_l_3518_;
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_v_3615_);
lean_inc(v_k_3614_);
lean_dec(v_l_3518_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3629_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3619_ = lean_unsigned_to_nat(3u);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 4, v_r_3519_);
lean_ctor_set(v___x_3617_, 3, v_r_3519_);
lean_ctor_set(v___x_3617_, 2, v_v_3613_);
lean_ctor_set(v___x_3617_, 1, v_k_3612_);
lean_ctor_set(v___x_3617_, 0, v___x_3520_);
v___x_3621_ = v___x_3617_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v_k_3612_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v_v_3613_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v_r_3519_);
v___x_3621_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 3, v_r_3519_);
lean_ctor_set(v___x_3599_, 0, v___x_3520_);
v___x_3623_ = v___x_3599_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_r_3519_);
v___x_3623_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3625_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v___x_3623_);
lean_ctor_set(v___x_3523_, 3, v___x_3621_);
lean_ctor_set(v___x_3523_, 2, v_v_3615_);
lean_ctor_set(v___x_3523_, 1, v_k_3614_);
lean_ctor_set(v___x_3523_, 0, v___x_3619_);
v___x_3625_ = v___x_3523_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3614_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3615_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3519_) == 0)
{
lean_object* v_k_3633_; lean_object* v_v_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_dec(v_size_3515_);
v_k_3633_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_k_3633_);
v_v_3634_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_v_3634_);
lean_dec_ref(v___x_3525_);
v___x_3635_ = lean_unsigned_to_nat(3u);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 4, v_l_3518_);
lean_ctor_set(v___x_3599_, 2, v_v_3634_);
lean_ctor_set(v___x_3599_, 1, v_k_3633_);
lean_ctor_set(v___x_3599_, 0, v___x_3520_);
v___x_3637_ = v___x_3599_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3641_, 3, v_l_3518_);
lean_ctor_set(v_reuseFailAlloc_3641_, 4, v_l_3518_);
v___x_3637_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v_r_3519_);
lean_ctor_set(v___x_3523_, 3, v___x_3637_);
lean_ctor_set(v___x_3523_, 2, v_v_3517_);
lean_ctor_set(v___x_3523_, 1, v_k_3516_);
lean_ctor_set(v___x_3523_, 0, v___x_3635_);
v___x_3639_ = v___x_3523_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3640_, 3, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_r_3519_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
else
{
lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v___x_3645_; 
v_k_3642_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_k_3642_);
v_v_3643_ = lean_ctor_get(v___x_3525_, 1);
lean_inc(v_v_3643_);
lean_dec_ref(v___x_3525_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 3, v_r_3519_);
v___x_3645_ = v___x_3599_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_size_3515_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_r_3519_);
v___x_3645_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3646_ = lean_unsigned_to_nat(2u);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 4, v___x_3645_);
lean_ctor_set(v___x_3523_, 3, v_r_3519_);
lean_ctor_set(v___x_3523_, 2, v_v_3643_);
lean_ctor_set(v___x_3523_, 1, v_k_3642_);
lean_ctor_set(v___x_3523_, 0, v___x_3646_);
v___x_3648_ = v___x_3523_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3646_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3642_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3643_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v___x_3645_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
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
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3815_; 
lean_inc(v_r_3519_);
lean_inc(v_v_3517_);
lean_inc(v_k_3516_);
v_isSharedCheck_3815_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; 
v_unused_3816_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_r_3331_, 2);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_r_3331_, 1);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3820_);
v___x_3664_ = v_r_3331_;
v_isShared_3665_ = v_isSharedCheck_3815_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_r_3331_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3815_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v_tree_3667_; 
v___x_3666_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3516_, v_v_3517_, v_l_3518_, v_r_3519_);
v_tree_3667_ = lean_ctor_get(v___x_3666_, 2);
lean_inc(v_tree_3667_);
if (lean_obj_tag(v_tree_3667_) == 0)
{
lean_object* v_k_3668_; lean_object* v_v_3669_; lean_object* v_size_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_k_3668_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_k_3668_);
v_v_3669_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_v_3669_);
lean_dec_ref(v___x_3666_);
v_size_3670_ = lean_ctor_get(v_tree_3667_, 0);
v___x_3671_ = lean_unsigned_to_nat(3u);
v___x_3672_ = lean_nat_mul(v___x_3671_, v_size_3670_);
v___x_3673_ = lean_nat_dec_lt(v___x_3672_, v_size_3510_);
lean_dec(v___x_3672_);
if (v___x_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3677_; 
lean_dec(v_r_3514_);
v___x_3674_ = lean_nat_add(v___x_3520_, v_size_3510_);
v___x_3675_ = lean_nat_add(v___x_3674_, v_size_3670_);
lean_dec(v___x_3674_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_tree_3667_);
lean_ctor_set(v___x_3664_, 3, v_l_3330_);
lean_ctor_set(v___x_3664_, 2, v_v_3669_);
lean_ctor_set(v___x_3664_, 1, v_k_3668_);
lean_ctor_set(v___x_3664_, 0, v___x_3675_);
v___x_3677_ = v___x_3664_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3678_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3678_, 4, v_tree_3667_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
else
{
lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3744_; 
lean_inc(v_l_3513_);
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
lean_inc(v_size_3510_);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3745_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_l_3330_, 2);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_l_3330_, 1);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3749_);
v___x_3680_ = v_l_3330_;
v_isShared_3681_ = v_isSharedCheck_3744_;
goto v_resetjp_3679_;
}
else
{
lean_dec(v_l_3330_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3744_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_size_3682_; lean_object* v_size_3683_; lean_object* v_k_3684_; lean_object* v_v_3685_; lean_object* v_l_3686_; lean_object* v_r_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_size_3682_ = lean_ctor_get(v_l_3513_, 0);
v_size_3683_ = lean_ctor_get(v_r_3514_, 0);
v_k_3684_ = lean_ctor_get(v_r_3514_, 1);
v_v_3685_ = lean_ctor_get(v_r_3514_, 2);
v_l_3686_ = lean_ctor_get(v_r_3514_, 3);
v_r_3687_ = lean_ctor_get(v_r_3514_, 4);
v___x_3688_ = lean_unsigned_to_nat(2u);
v___x_3689_ = lean_nat_mul(v___x_3688_, v_size_3682_);
v___x_3690_ = lean_nat_dec_lt(v_size_3683_, v___x_3689_);
lean_dec(v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3728_; 
lean_inc(v_r_3687_);
lean_inc(v_l_3686_);
lean_inc(v_v_3685_);
lean_inc(v_k_3684_);
lean_del_object(v___x_3680_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_r_3514_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3729_ = lean_ctor_get(v_r_3514_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_r_3514_, 3);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_r_3514_, 2);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3514_, 1);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3514_, 0);
lean_dec(v_unused_3733_);
v___x_3692_ = v_r_3514_;
v_isShared_3693_ = v_isSharedCheck_3728_;
goto v_resetjp_3691_;
}
else
{
lean_dec(v_r_3514_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3728_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___x_3716_; lean_object* v___y_3718_; 
v___x_3694_ = lean_nat_add(v___x_3520_, v_size_3510_);
lean_dec(v_size_3510_);
v___x_3695_ = lean_nat_add(v___x_3694_, v_size_3670_);
lean_dec(v___x_3694_);
v___x_3716_ = lean_nat_add(v___x_3520_, v_size_3682_);
if (lean_obj_tag(v_l_3686_) == 0)
{
lean_object* v_size_3726_; 
v_size_3726_ = lean_ctor_get(v_l_3686_, 0);
lean_inc(v_size_3726_);
v___y_3718_ = v_size_3726_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v___y_3718_ = v___x_3727_;
goto v___jp_3717_;
}
v___jp_3696_:
{
lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3700_ = lean_nat_add(v___y_3697_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec(v___y_3697_);
lean_inc_ref(v_tree_3667_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 4, v_tree_3667_);
lean_ctor_set(v___x_3692_, 3, v_r_3687_);
lean_ctor_set(v___x_3692_, 2, v_v_3669_);
lean_ctor_set(v___x_3692_, 1, v_k_3668_);
lean_ctor_set(v___x_3692_, 0, v___x_3700_);
v___x_3702_ = v___x_3692_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_r_3687_);
lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_tree_3667_);
v___x_3702_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_isSharedCheck_3709_ = !lean_is_exclusive(v_tree_3667_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; lean_object* v_unused_3714_; 
v_unused_3710_ = lean_ctor_get(v_tree_3667_, 4);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_tree_3667_, 3);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_tree_3667_, 2);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_tree_3667_, 1);
lean_dec(v_unused_3713_);
v_unused_3714_ = lean_ctor_get(v_tree_3667_, 0);
lean_dec(v_unused_3714_);
v___x_3704_ = v_tree_3667_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v_tree_3667_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 4, v___x_3702_);
lean_ctor_set(v___x_3704_, 3, v___y_3698_);
lean_ctor_set(v___x_3704_, 2, v_v_3685_);
lean_ctor_set(v___x_3704_, 1, v_k_3684_);
lean_ctor_set(v___x_3704_, 0, v___x_3695_);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_k_3684_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_v_3685_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v___y_3698_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v___x_3702_);
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
v___jp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_nat_add(v___x_3716_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec(v___x_3716_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_l_3686_);
lean_ctor_set(v___x_3664_, 3, v_l_3513_);
lean_ctor_set(v___x_3664_, 2, v_v_3512_);
lean_ctor_set(v___x_3664_, 1, v_k_3511_);
lean_ctor_set(v___x_3664_, 0, v___x_3719_);
v___x_3721_ = v___x_3664_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_l_3686_);
v___x_3721_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_nat_add(v___x_3520_, v_size_3670_);
if (lean_obj_tag(v_r_3687_) == 0)
{
lean_object* v_size_3723_; 
v_size_3723_ = lean_ctor_get(v_r_3687_, 0);
lean_inc(v_size_3723_);
v___y_3697_ = v___x_3722_;
v___y_3698_ = v___x_3721_;
v___y_3699_ = v_size_3723_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
v___y_3697_ = v___x_3722_;
v___y_3698_ = v___x_3721_;
v___y_3699_ = v___x_3724_;
goto v___jp_3696_;
}
}
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3734_ = lean_nat_add(v___x_3520_, v_size_3510_);
lean_dec(v_size_3510_);
v___x_3735_ = lean_nat_add(v___x_3734_, v_size_3670_);
lean_dec(v___x_3734_);
v___x_3736_ = lean_nat_add(v___x_3520_, v_size_3670_);
v___x_3737_ = lean_nat_add(v___x_3736_, v_size_3683_);
lean_dec(v___x_3736_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_tree_3667_);
lean_ctor_set(v___x_3664_, 3, v_r_3514_);
lean_ctor_set(v___x_3664_, 2, v_v_3669_);
lean_ctor_set(v___x_3664_, 1, v_k_3668_);
lean_ctor_set(v___x_3664_, 0, v___x_3737_);
v___x_3739_ = v___x_3664_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v_r_3514_);
lean_ctor_set(v_reuseFailAlloc_3743_, 4, v_tree_3667_);
v___x_3739_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 4, v___x_3739_);
lean_ctor_set(v___x_3680_, 0, v___x_3735_);
v___x_3741_ = v___x_3680_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3513_) == 0)
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3773_; 
lean_inc_ref(v_l_3513_);
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
lean_inc(v_size_3510_);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; lean_object* v_unused_3775_; lean_object* v_unused_3776_; lean_object* v_unused_3777_; lean_object* v_unused_3778_; 
v_unused_3774_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v_l_3330_, 2);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v_l_3330_, 1);
lean_dec(v_unused_3777_);
v_unused_3778_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3778_);
v___x_3751_ = v_l_3330_;
v_isShared_3752_ = v_isSharedCheck_3773_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v_l_3330_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3773_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
if (lean_obj_tag(v_r_3514_) == 0)
{
lean_object* v_k_3753_; lean_object* v_v_3754_; lean_object* v_size_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v_k_3753_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_k_3753_);
v_v_3754_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_v_3754_);
lean_dec_ref(v___x_3666_);
v_size_3755_ = lean_ctor_get(v_r_3514_, 0);
v___x_3756_ = lean_nat_add(v___x_3520_, v_size_3510_);
lean_dec(v_size_3510_);
v___x_3757_ = lean_nat_add(v___x_3520_, v_size_3755_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_tree_3667_);
lean_ctor_set(v___x_3664_, 3, v_r_3514_);
lean_ctor_set(v___x_3664_, 2, v_v_3754_);
lean_ctor_set(v___x_3664_, 1, v_k_3753_);
lean_ctor_set(v___x_3664_, 0, v___x_3757_);
v___x_3759_ = v___x_3664_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3753_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3754_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_r_3514_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_tree_3667_);
v___x_3759_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3761_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 4, v___x_3759_);
lean_ctor_set(v___x_3751_, 0, v___x_3756_);
v___x_3761_ = v___x_3751_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
else
{
lean_object* v_k_3764_; lean_object* v_v_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec(v_size_3510_);
v_k_3764_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_k_3764_);
v_v_3765_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_v_3765_);
lean_dec_ref(v___x_3666_);
v___x_3766_ = lean_unsigned_to_nat(3u);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_r_3514_);
lean_ctor_set(v___x_3664_, 3, v_r_3514_);
lean_ctor_set(v___x_3664_, 2, v_v_3765_);
lean_ctor_set(v___x_3664_, 1, v_k_3764_);
lean_ctor_set(v___x_3664_, 0, v___x_3520_);
v___x_3768_ = v___x_3664_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3764_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3765_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_r_3514_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_r_3514_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 4, v___x_3768_);
lean_ctor_set(v___x_3751_, 0, v___x_3766_);
v___x_3770_ = v___x_3751_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3514_) == 0)
{
lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3803_; 
lean_inc(v_l_3513_);
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
v_isSharedCheck_3803_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3803_ == 0)
{
lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; lean_object* v_unused_3808_; 
v_unused_3804_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_l_3330_, 2);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_l_3330_, 1);
lean_dec(v_unused_3807_);
v_unused_3808_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3808_);
v___x_3780_ = v_l_3330_;
v_isShared_3781_ = v_isSharedCheck_3803_;
goto v_resetjp_3779_;
}
else
{
lean_dec(v_l_3330_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3803_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_k_3782_; lean_object* v_v_3783_; lean_object* v_k_3784_; lean_object* v_v_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3799_; 
v_k_3782_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_k_3782_);
v_v_3783_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_v_3783_);
lean_dec_ref(v___x_3666_);
v_k_3784_ = lean_ctor_get(v_r_3514_, 1);
v_v_3785_ = lean_ctor_get(v_r_3514_, 2);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_r_3514_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; lean_object* v_unused_3801_; lean_object* v_unused_3802_; 
v_unused_3800_ = lean_ctor_get(v_r_3514_, 4);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_r_3514_, 3);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_r_3514_, 0);
lean_dec(v_unused_3802_);
v___x_3787_ = v_r_3514_;
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_v_3785_);
lean_inc(v_k_3784_);
lean_dec(v_r_3514_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3799_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3789_ = lean_unsigned_to_nat(3u);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 4, v_l_3513_);
lean_ctor_set(v___x_3787_, 3, v_l_3513_);
lean_ctor_set(v___x_3787_, 2, v_v_3512_);
lean_ctor_set(v___x_3787_, 1, v_k_3511_);
lean_ctor_set(v___x_3787_, 0, v___x_3520_);
v___x_3791_ = v___x_3787_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_l_3513_);
v___x_3791_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_l_3513_);
lean_ctor_set(v___x_3664_, 3, v_l_3513_);
lean_ctor_set(v___x_3664_, 2, v_v_3783_);
lean_ctor_set(v___x_3664_, 1, v_k_3782_);
lean_ctor_set(v___x_3664_, 0, v___x_3520_);
v___x_3793_ = v___x_3664_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_l_3513_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v_l_3513_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 4, v___x_3793_);
lean_ctor_set(v___x_3780_, 3, v___x_3791_);
lean_ctor_set(v___x_3780_, 2, v_v_3785_);
lean_ctor_set(v___x_3780_, 1, v_k_3784_);
lean_ctor_set(v___x_3780_, 0, v___x_3789_);
v___x_3795_ = v___x_3780_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3784_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3785_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
else
{
lean_object* v_k_3809_; lean_object* v_v_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v_k_3809_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_k_3809_);
v_v_3810_ = lean_ctor_get(v___x_3666_, 1);
lean_inc(v_v_3810_);
lean_dec_ref(v___x_3666_);
v___x_3811_ = lean_unsigned_to_nat(2u);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_r_3514_);
lean_ctor_set(v___x_3664_, 3, v_l_3330_);
lean_ctor_set(v___x_3664_, 2, v_v_3810_);
lean_ctor_set(v___x_3664_, 1, v_k_3809_);
lean_ctor_set(v___x_3664_, 0, v___x_3811_);
v___x_3813_ = v___x_3664_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3809_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3810_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_r_3514_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
}
else
{
return v_l_3330_;
}
}
else
{
return v_r_3331_;
}
}
default: 
{
lean_object* v_impl_3821_; lean_object* v___x_3822_; 
v_impl_3821_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3326_, v_r_3331_);
v___x_3822_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3821_) == 0)
{
if (lean_obj_tag(v_l_3330_) == 0)
{
lean_object* v_size_3823_; lean_object* v_size_3824_; lean_object* v_k_3825_; lean_object* v_v_3826_; lean_object* v_l_3827_; lean_object* v_r_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v_size_3823_ = lean_ctor_get(v_impl_3821_, 0);
lean_inc(v_size_3823_);
v_size_3824_ = lean_ctor_get(v_l_3330_, 0);
v_k_3825_ = lean_ctor_get(v_l_3330_, 1);
v_v_3826_ = lean_ctor_get(v_l_3330_, 2);
v_l_3827_ = lean_ctor_get(v_l_3330_, 3);
v_r_3828_ = lean_ctor_get(v_l_3330_, 4);
lean_inc(v_r_3828_);
v___x_3829_ = lean_unsigned_to_nat(3u);
v___x_3830_ = lean_nat_mul(v___x_3829_, v_size_3823_);
v___x_3831_ = lean_nat_dec_lt(v___x_3830_, v_size_3824_);
lean_dec(v___x_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3835_; 
lean_dec(v_r_3828_);
v___x_3832_ = lean_nat_add(v___x_3822_, v_size_3824_);
v___x_3833_ = lean_nat_add(v___x_3832_, v_size_3823_);
lean_dec(v_size_3823_);
lean_dec(v___x_3832_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_impl_3821_);
lean_ctor_set(v___x_3333_, 0, v___x_3833_);
v___x_3835_ = v___x_3333_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3836_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3836_, 4, v_impl_3821_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
else
{
lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3902_; 
lean_inc(v_l_3827_);
lean_inc(v_v_3826_);
lean_inc(v_k_3825_);
lean_inc(v_size_3824_);
v_isSharedCheck_3902_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3902_ == 0)
{
lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; lean_object* v_unused_3907_; 
v_unused_3903_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_l_3330_, 2);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_l_3330_, 1);
lean_dec(v_unused_3906_);
v_unused_3907_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3907_);
v___x_3838_ = v_l_3330_;
v_isShared_3839_ = v_isSharedCheck_3902_;
goto v_resetjp_3837_;
}
else
{
lean_dec(v_l_3330_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3902_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v_size_3840_; lean_object* v_size_3841_; lean_object* v_k_3842_; lean_object* v_v_3843_; lean_object* v_l_3844_; lean_object* v_r_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_size_3840_ = lean_ctor_get(v_l_3827_, 0);
v_size_3841_ = lean_ctor_get(v_r_3828_, 0);
v_k_3842_ = lean_ctor_get(v_r_3828_, 1);
v_v_3843_ = lean_ctor_get(v_r_3828_, 2);
v_l_3844_ = lean_ctor_get(v_r_3828_, 3);
v_r_3845_ = lean_ctor_get(v_r_3828_, 4);
v___x_3846_ = lean_unsigned_to_nat(2u);
v___x_3847_ = lean_nat_mul(v___x_3846_, v_size_3840_);
v___x_3848_ = lean_nat_dec_lt(v_size_3841_, v___x_3847_);
lean_dec(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3877_; 
lean_inc(v_r_3845_);
lean_inc(v_l_3844_);
lean_inc(v_v_3843_);
lean_inc(v_k_3842_);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_r_3828_);
if (v_isSharedCheck_3877_ == 0)
{
lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; lean_object* v_unused_3882_; 
v_unused_3878_ = lean_ctor_get(v_r_3828_, 4);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_r_3828_, 3);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_r_3828_, 2);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_r_3828_, 1);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_r_3828_, 0);
lean_dec(v_unused_3882_);
v___x_3850_ = v_r_3828_;
v_isShared_3851_ = v_isSharedCheck_3877_;
goto v_resetjp_3849_;
}
else
{
lean_dec(v_r_3828_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3877_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___x_3865_; lean_object* v___y_3867_; 
v___x_3852_ = lean_nat_add(v___x_3822_, v_size_3824_);
lean_dec(v_size_3824_);
v___x_3853_ = lean_nat_add(v___x_3852_, v_size_3823_);
lean_dec(v___x_3852_);
v___x_3865_ = lean_nat_add(v___x_3822_, v_size_3840_);
if (lean_obj_tag(v_l_3844_) == 0)
{
lean_object* v_size_3875_; 
v_size_3875_ = lean_ctor_get(v_l_3844_, 0);
lean_inc(v_size_3875_);
v___y_3867_ = v_size_3875_;
goto v___jp_3866_;
}
else
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_unsigned_to_nat(0u);
v___y_3867_ = v___x_3876_;
goto v___jp_3866_;
}
v___jp_3854_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_nat_add(v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec(v___y_3856_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 4, v_impl_3821_);
lean_ctor_set(v___x_3850_, 3, v_r_3845_);
lean_ctor_set(v___x_3850_, 2, v_v_3329_);
lean_ctor_set(v___x_3850_, 1, v_k_3328_);
lean_ctor_set(v___x_3850_, 0, v___x_3858_);
v___x_3860_ = v___x_3850_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_r_3845_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_impl_3821_);
v___x_3860_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3862_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 4, v___x_3860_);
lean_ctor_set(v___x_3838_, 3, v___y_3855_);
lean_ctor_set(v___x_3838_, 2, v_v_3843_);
lean_ctor_set(v___x_3838_, 1, v_k_3842_);
lean_ctor_set(v___x_3838_, 0, v___x_3853_);
v___x_3862_ = v___x_3838_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3853_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_k_3842_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_v_3843_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v___y_3855_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
v___jp_3866_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_nat_add(v___x_3865_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec(v___x_3865_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_l_3844_);
lean_ctor_set(v___x_3333_, 3, v_l_3827_);
lean_ctor_set(v___x_3333_, 2, v_v_3826_);
lean_ctor_set(v___x_3333_, 1, v_k_3825_);
lean_ctor_set(v___x_3333_, 0, v___x_3868_);
v___x_3870_ = v___x_3333_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_k_3825_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_v_3826_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_l_3827_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v_l_3844_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_nat_add(v___x_3822_, v_size_3823_);
lean_dec(v_size_3823_);
if (lean_obj_tag(v_r_3845_) == 0)
{
lean_object* v_size_3872_; 
v_size_3872_ = lean_ctor_get(v_r_3845_, 0);
lean_inc(v_size_3872_);
v___y_3855_ = v___x_3870_;
v___y_3856_ = v___x_3871_;
v___y_3857_ = v_size_3872_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3873_; 
v___x_3873_ = lean_unsigned_to_nat(0u);
v___y_3855_ = v___x_3870_;
v___y_3856_ = v___x_3871_;
v___y_3857_ = v___x_3873_;
goto v___jp_3854_;
}
}
}
}
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3888_; 
lean_del_object(v___x_3333_);
v___x_3883_ = lean_nat_add(v___x_3822_, v_size_3824_);
lean_dec(v_size_3824_);
v___x_3884_ = lean_nat_add(v___x_3883_, v_size_3823_);
lean_dec(v___x_3883_);
v___x_3885_ = lean_nat_add(v___x_3822_, v_size_3823_);
lean_dec(v_size_3823_);
v___x_3886_ = lean_nat_add(v___x_3885_, v_size_3841_);
lean_dec(v___x_3885_);
lean_inc_ref(v_impl_3821_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 4, v_impl_3821_);
lean_ctor_set(v___x_3838_, 3, v_r_3828_);
lean_ctor_set(v___x_3838_, 2, v_v_3329_);
lean_ctor_set(v___x_3838_, 1, v_k_3328_);
lean_ctor_set(v___x_3838_, 0, v___x_3886_);
v___x_3888_ = v___x_3838_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v_r_3828_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v_impl_3821_);
v___x_3888_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_isSharedCheck_3895_ = !lean_is_exclusive(v_impl_3821_);
if (v_isSharedCheck_3895_ == 0)
{
lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; lean_object* v_unused_3900_; 
v_unused_3896_ = lean_ctor_get(v_impl_3821_, 4);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3821_, 3);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3821_, 2);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_impl_3821_, 1);
lean_dec(v_unused_3899_);
v_unused_3900_ = lean_ctor_get(v_impl_3821_, 0);
lean_dec(v_unused_3900_);
v___x_3890_ = v_impl_3821_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_dec(v_impl_3821_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 4, v___x_3888_);
lean_ctor_set(v___x_3890_, 3, v_l_3827_);
lean_ctor_set(v___x_3890_, 2, v_v_3826_);
lean_ctor_set(v___x_3890_, 1, v_k_3825_);
lean_ctor_set(v___x_3890_, 0, v___x_3884_);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_k_3825_);
lean_ctor_set(v_reuseFailAlloc_3894_, 2, v_v_3826_);
lean_ctor_set(v_reuseFailAlloc_3894_, 3, v_l_3827_);
lean_ctor_set(v_reuseFailAlloc_3894_, 4, v___x_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v_size_3908_ = lean_ctor_get(v_impl_3821_, 0);
lean_inc(v_size_3908_);
v___x_3909_ = lean_nat_add(v___x_3822_, v_size_3908_);
lean_dec(v_size_3908_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_impl_3821_);
lean_ctor_set(v___x_3333_, 0, v___x_3909_);
v___x_3911_ = v___x_3333_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_impl_3821_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
if (lean_obj_tag(v_l_3330_) == 0)
{
lean_object* v_l_3913_; 
v_l_3913_ = lean_ctor_get(v_l_3330_, 3);
if (lean_obj_tag(v_l_3913_) == 0)
{
lean_object* v_r_3914_; 
lean_inc_ref(v_l_3913_);
v_r_3914_ = lean_ctor_get(v_l_3330_, 4);
lean_inc(v_r_3914_);
if (lean_obj_tag(v_r_3914_) == 0)
{
lean_object* v_size_3915_; lean_object* v_k_3916_; lean_object* v_v_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3930_; 
v_size_3915_ = lean_ctor_get(v_l_3330_, 0);
v_k_3916_ = lean_ctor_get(v_l_3330_, 1);
v_v_3917_ = lean_ctor_get(v_l_3330_, 2);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; lean_object* v_unused_3932_; 
v_unused_3931_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3932_);
v___x_3919_ = v_l_3330_;
v_isShared_3920_ = v_isSharedCheck_3930_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_v_3917_);
lean_inc(v_k_3916_);
lean_inc(v_size_3915_);
lean_dec(v_l_3330_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3930_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v_size_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
v_size_3921_ = lean_ctor_get(v_r_3914_, 0);
v___x_3922_ = lean_nat_add(v___x_3822_, v_size_3915_);
lean_dec(v_size_3915_);
v___x_3923_ = lean_nat_add(v___x_3822_, v_size_3921_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 4, v_impl_3821_);
lean_ctor_set(v___x_3919_, 3, v_r_3914_);
lean_ctor_set(v___x_3919_, 2, v_v_3329_);
lean_ctor_set(v___x_3919_, 1, v_k_3328_);
lean_ctor_set(v___x_3919_, 0, v___x_3923_);
v___x_3925_ = v___x_3919_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_r_3914_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_impl_3821_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3927_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v___x_3925_);
lean_ctor_set(v___x_3333_, 3, v_l_3913_);
lean_ctor_set(v___x_3333_, 2, v_v_3917_);
lean_ctor_set(v___x_3333_, 1, v_k_3916_);
lean_ctor_set(v___x_3333_, 0, v___x_3922_);
v___x_3927_ = v___x_3333_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_k_3916_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_v_3917_);
lean_ctor_set(v_reuseFailAlloc_3928_, 3, v_l_3913_);
lean_ctor_set(v_reuseFailAlloc_3928_, 4, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
else
{
lean_object* v_k_3933_; lean_object* v_v_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3945_; 
v_k_3933_ = lean_ctor_get(v_l_3330_, 1);
v_v_3934_ = lean_ctor_get(v_l_3330_, 2);
v_isSharedCheck_3945_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3945_ == 0)
{
lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; 
v_unused_3946_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3948_);
v___x_3936_ = v_l_3330_;
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_v_3934_);
lean_inc(v_k_3933_);
lean_dec(v_l_3330_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3938_ = lean_unsigned_to_nat(3u);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 3, v_r_3914_);
lean_ctor_set(v___x_3936_, 2, v_v_3329_);
lean_ctor_set(v___x_3936_, 1, v_k_3328_);
lean_ctor_set(v___x_3936_, 0, v___x_3822_);
v___x_3940_ = v___x_3936_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3944_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3944_, 3, v_r_3914_);
lean_ctor_set(v_reuseFailAlloc_3944_, 4, v_r_3914_);
v___x_3940_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3942_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v___x_3940_);
lean_ctor_set(v___x_3333_, 3, v_l_3913_);
lean_ctor_set(v___x_3333_, 2, v_v_3934_);
lean_ctor_set(v___x_3333_, 1, v_k_3933_);
lean_ctor_set(v___x_3333_, 0, v___x_3938_);
v___x_3942_ = v___x_3333_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_k_3933_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_v_3934_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_l_3913_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
else
{
lean_object* v_r_3949_; 
v_r_3949_ = lean_ctor_get(v_l_3330_, 4);
lean_inc(v_r_3949_);
if (lean_obj_tag(v_r_3949_) == 0)
{
lean_object* v_k_3950_; lean_object* v_v_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3974_; 
lean_inc(v_l_3913_);
v_k_3950_ = lean_ctor_get(v_l_3330_, 1);
v_v_3951_ = lean_ctor_get(v_l_3330_, 2);
v_isSharedCheck_3974_ = !lean_is_exclusive(v_l_3330_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; lean_object* v_unused_3976_; lean_object* v_unused_3977_; 
v_unused_3975_ = lean_ctor_get(v_l_3330_, 4);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_l_3330_, 3);
lean_dec(v_unused_3976_);
v_unused_3977_ = lean_ctor_get(v_l_3330_, 0);
lean_dec(v_unused_3977_);
v___x_3953_ = v_l_3330_;
v_isShared_3954_ = v_isSharedCheck_3974_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_v_3951_);
lean_inc(v_k_3950_);
lean_dec(v_l_3330_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3974_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v_k_3955_; lean_object* v_v_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3970_; 
v_k_3955_ = lean_ctor_get(v_r_3949_, 1);
v_v_3956_ = lean_ctor_get(v_r_3949_, 2);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_r_3949_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; lean_object* v_unused_3972_; lean_object* v_unused_3973_; 
v_unused_3971_ = lean_ctor_get(v_r_3949_, 4);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_r_3949_, 3);
lean_dec(v_unused_3972_);
v_unused_3973_ = lean_ctor_get(v_r_3949_, 0);
lean_dec(v_unused_3973_);
v___x_3958_ = v_r_3949_;
v_isShared_3959_ = v_isSharedCheck_3970_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_v_3956_);
lean_inc(v_k_3955_);
lean_dec(v_r_3949_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3970_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = lean_unsigned_to_nat(3u);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 4, v_l_3913_);
lean_ctor_set(v___x_3958_, 3, v_l_3913_);
lean_ctor_set(v___x_3958_, 2, v_v_3951_);
lean_ctor_set(v___x_3958_, 1, v_k_3950_);
lean_ctor_set(v___x_3958_, 0, v___x_3822_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3969_, 1, v_k_3950_);
lean_ctor_set(v_reuseFailAlloc_3969_, 2, v_v_3951_);
lean_ctor_set(v_reuseFailAlloc_3969_, 3, v_l_3913_);
lean_ctor_set(v_reuseFailAlloc_3969_, 4, v_l_3913_);
v___x_3962_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3964_; 
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 4, v_l_3913_);
lean_ctor_set(v___x_3953_, 2, v_v_3329_);
lean_ctor_set(v___x_3953_, 1, v_k_3328_);
lean_ctor_set(v___x_3953_, 0, v___x_3822_);
v___x_3964_ = v___x_3953_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_l_3913_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_l_3913_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3966_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v___x_3964_);
lean_ctor_set(v___x_3333_, 3, v___x_3962_);
lean_ctor_set(v___x_3333_, 2, v_v_3956_);
lean_ctor_set(v___x_3333_, 1, v_k_3955_);
lean_ctor_set(v___x_3333_, 0, v___x_3960_);
v___x_3966_ = v___x_3333_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3955_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3956_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3978_ = lean_unsigned_to_nat(2u);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_r_3949_);
lean_ctor_set(v___x_3333_, 0, v___x_3978_);
v___x_3980_ = v___x_3333_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v_r_3949_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
else
{
lean_object* v___x_3983_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 4, v_l_3330_);
lean_ctor_set(v___x_3333_, 0, v___x_3822_);
v___x_3983_ = v___x_3333_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3822_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3984_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3984_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3984_, 4, v_l_3330_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
}
}
else
{
return v_t_3327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3987_, lean_object* v_t_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3987_, v_t_3988_);
lean_dec(v_k_3987_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3990_, lean_object* v_x_3991_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3990_, v_x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3993_, lean_object* v_x_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3993_, v_x_3994_);
lean_dec(v_declName_3993_);
return v_res_3995_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3998_ = l_Lean_stringToMessageData(v___x_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
lean_object* v___x_4007_; lean_object* v_env_4008_; lean_object* v___f_4009_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___x_4053_; 
v___x_4007_ = lean_st_ref_get(v___y_4005_);
v_env_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc_ref(v_env_4008_);
lean_dec(v___x_4007_);
lean_inc(v_declName_3999_);
v___f_4009_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4009_, 0, v_declName_3999_);
v___x_4053_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4008_, v_declName_3999_);
lean_dec_ref(v_env_4008_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_dec(v_declName_3999_);
v___y_4011_ = v___y_4003_;
v___y_4012_ = v___y_4005_;
goto v___jp_4010_;
}
else
{
uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
lean_dec_ref_known(v___x_4053_, 1);
lean_dec_ref(v___f_4009_);
v___x_4054_ = 0;
v___x_4055_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4056_ = l_Lean_MessageData_ofConstName(v_declName_3999_, v___x_4054_);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4059_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
return v___x_4060_;
}
v___jp_4010_:
{
lean_object* v___x_4013_; lean_object* v_env_4014_; lean_object* v_nextMacroScope_4015_; lean_object* v_ngen_4016_; lean_object* v_auxDeclNGen_4017_; lean_object* v_traceState_4018_; lean_object* v_messages_4019_; lean_object* v_infoState_4020_; lean_object* v_snapshotTasks_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4051_; 
v___x_4013_ = lean_st_ref_take(v___y_4012_);
v_env_4014_ = lean_ctor_get(v___x_4013_, 0);
v_nextMacroScope_4015_ = lean_ctor_get(v___x_4013_, 1);
v_ngen_4016_ = lean_ctor_get(v___x_4013_, 2);
v_auxDeclNGen_4017_ = lean_ctor_get(v___x_4013_, 3);
v_traceState_4018_ = lean_ctor_get(v___x_4013_, 4);
v_messages_4019_ = lean_ctor_get(v___x_4013_, 6);
v_infoState_4020_ = lean_ctor_get(v___x_4013_, 7);
v_snapshotTasks_4021_ = lean_ctor_get(v___x_4013_, 8);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; 
v_unused_4052_ = lean_ctor_get(v___x_4013_, 5);
lean_dec(v_unused_4052_);
v___x_4023_ = v___x_4013_;
v_isShared_4024_ = v_isSharedCheck_4051_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_snapshotTasks_4021_);
lean_inc(v_infoState_4020_);
lean_inc(v_messages_4019_);
lean_inc(v_traceState_4018_);
lean_inc(v_auxDeclNGen_4017_);
lean_inc(v_ngen_4016_);
lean_inc(v_nextMacroScope_4015_);
lean_inc(v_env_4014_);
lean_dec(v___x_4013_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4051_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4025_ = l_Lean_docStringExt;
v___x_4026_ = lean_box(2);
v___x_4027_ = lean_box(0);
v___x_4028_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4025_, v_env_4014_, v___f_4009_, v___x_4026_, v___x_4027_);
v___x_4029_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 5, v___x_4029_);
lean_ctor_set(v___x_4023_, 0, v___x_4028_);
v___x_4031_ = v___x_4023_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4050_, 1, v_nextMacroScope_4015_);
lean_ctor_set(v_reuseFailAlloc_4050_, 2, v_ngen_4016_);
lean_ctor_set(v_reuseFailAlloc_4050_, 3, v_auxDeclNGen_4017_);
lean_ctor_set(v_reuseFailAlloc_4050_, 4, v_traceState_4018_);
lean_ctor_set(v_reuseFailAlloc_4050_, 5, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4050_, 6, v_messages_4019_);
lean_ctor_set(v_reuseFailAlloc_4050_, 7, v_infoState_4020_);
lean_ctor_set(v_reuseFailAlloc_4050_, 8, v_snapshotTasks_4021_);
v___x_4031_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v_mctx_4034_; lean_object* v_zetaDeltaFVarIds_4035_; lean_object* v_postponed_4036_; lean_object* v_diag_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4048_; 
v___x_4032_ = lean_st_ref_put(v___y_4012_, v___x_4031_);
v___x_4033_ = lean_st_ref_take(v___y_4011_);
v_mctx_4034_ = lean_ctor_get(v___x_4033_, 0);
v_zetaDeltaFVarIds_4035_ = lean_ctor_get(v___x_4033_, 2);
v_postponed_4036_ = lean_ctor_get(v___x_4033_, 3);
v_diag_4037_ = lean_ctor_get(v___x_4033_, 4);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4048_ == 0)
{
lean_object* v_unused_4049_; 
v_unused_4049_ = lean_ctor_get(v___x_4033_, 1);
lean_dec(v_unused_4049_);
v___x_4039_ = v___x_4033_;
v_isShared_4040_ = v_isSharedCheck_4048_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_diag_4037_);
lean_inc(v_postponed_4036_);
lean_inc(v_zetaDeltaFVarIds_4035_);
lean_inc(v_mctx_4034_);
lean_dec(v___x_4033_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4048_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; lean_object* v___x_4043_; 
v___x_4041_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v___x_4041_);
v___x_4043_ = v___x_4039_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_mctx_4034_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4047_, 2, v_zetaDeltaFVarIds_4035_);
lean_ctor_set(v_reuseFailAlloc_4047_, 3, v_postponed_4036_);
lean_ctor_set(v_reuseFailAlloc_4047_, 4, v_diag_4037_);
v___x_4043_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4044_ = lean_st_ref_put(v___y_4011_, v___x_4043_);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_res_4069_; 
v_res_4069_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
return v_res_4069_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4075_ = l_Lean_stringToMessageData(v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4081_ = l_Lean_stringToMessageData(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4090_; lean_object* v_env_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; 
v___x_4090_ = lean_st_ref_get(v_a_4088_);
v_env_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc_ref(v_env_4091_);
lean_dec(v___x_4090_);
v___x_4092_ = 1;
lean_inc(v_declName_4082_);
v___x_4093_ = l_Lean_findInternalDocString_x3f(v_env_4091_, v_declName_4082_, v___x_4092_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
if (lean_obj_tag(v_a_4094_) == 1)
{
lean_object* v_val_4095_; 
v_val_4095_ = lean_ctor_get(v_a_4094_, 0);
lean_inc(v_val_4095_);
lean_dec_ref_known(v_a_4094_, 1);
if (lean_obj_tag(v_val_4095_) == 0)
{
lean_object* v_val_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4118_; 
v_val_4096_ = lean_ctor_get(v_val_4095_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v_val_4095_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4098_ = v_val_4095_;
v_isShared_4099_ = v_isSharedCheck_4118_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_val_4096_);
lean_dec(v_val_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4118_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_removeBuiltinDocString(v_declName_4082_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref_known(v___x_4100_, 1);
lean_del_object(v___x_4098_);
lean_inc(v_declName_4082_);
v___x_4101_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v___x_4102_; 
lean_dec_ref_known(v___x_4101_, 1);
v___x_4102_ = l_Lean_addVersoDocStringFromString(v_declName_4082_, v_val_4096_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4102_;
}
else
{
lean_dec(v_val_4096_);
lean_dec(v_declName_4082_);
return v___x_4101_;
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v_val_4096_);
lean_dec(v_declName_4082_);
v_a_4103_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4105_ = v___x_4100_;
v_isShared_4106_ = v_isSharedCheck_4117_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4100_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4117_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v_ref_4107_; lean_object* v___x_4108_; lean_object* v___x_4110_; 
v_ref_4107_ = lean_ctor_get(v_a_4087_, 2);
v___x_4108_ = lean_io_error_to_string(v_a_4103_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set_tag(v___x_4098_, 3);
lean_ctor_set(v___x_4098_, 0, v___x_4108_);
v___x_4110_ = v___x_4098_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
v___x_4111_ = l_Lean_MessageData_ofFormat(v___x_4110_);
lean_inc(v_ref_4107_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_ref_4107_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
if (v_isShared_4106_ == 0)
{
lean_ctor_set(v___x_4105_, 0, v___x_4112_);
v___x_4114_ = v___x_4105_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
}
else
{
lean_object* v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_dec(v_val_4095_);
v___x_4119_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4120_ = 0;
v___x_4121_ = l_Lean_MessageData_ofConstName(v_declName_4082_, v___x_4120_);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4119_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4124_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4125_;
}
}
else
{
lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
lean_dec(v_a_4094_);
v___x_4126_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4127_ = 0;
v___x_4128_ = l_Lean_MessageData_ofConstName(v_declName_4082_, v___x_4127_);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4126_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4129_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4131_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4132_;
}
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v_declName_4082_);
v_a_4133_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4135_ = v___x_4093_;
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4093_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4145_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v_ref_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4143_; 
v_ref_4137_ = lean_ctor_get(v_a_4087_, 2);
v___x_4138_ = lean_io_error_to_string(v_a_4133_);
v___x_4139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
v___x_4140_ = l_Lean_MessageData_ofFormat(v___x_4139_);
lean_inc(v_ref_4137_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v_ref_4137_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v___x_4141_);
v___x_4143_ = v___x_4135_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_makeDocStringVerso(v_declName_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
lean_dec(v_a_4152_);
lean_dec_ref(v_a_4151_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4155_, lean_object* v_k_4156_, lean_object* v_t_4157_, lean_object* v_h_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4156_, v_t_4157_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4160_, lean_object* v_k_4161_, lean_object* v_t_4162_, lean_object* v_h_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4160_, v_k_4161_, v_t_4162_, v_h_4163_);
lean_dec(v_k_4161_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4165_, lean_object* v_binders_4166_, lean_object* v_docComment_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
uint8_t v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = l_Lean_isVersoDocComment(v_docComment_4167_);
v___x_4176_ = l_Lean_addDocStringOf(v___x_4175_, v_declName_4165_, v_binders_4166_, v_docComment_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4177_, lean_object* v_binders_4178_, lean_object* v_docComment_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l_Lean_addDocString(v_declName_4177_, v_binders_4178_, v_docComment_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4188_, lean_object* v_binders_4189_, lean_object* v_docString_x3f_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4190_) == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_dec(v_binders_4189_);
lean_dec(v_declName_4188_);
v___x_4198_ = lean_box(0);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
else
{
lean_object* v_val_4200_; lean_object* v___x_4201_; 
v_val_4200_ = lean_ctor_get(v_docString_x3f_4190_, 0);
lean_inc(v_val_4200_);
lean_dec_ref_known(v_docString_x3f_4190_, 1);
v___x_4201_ = l_Lean_addDocString(v_declName_4188_, v_binders_4189_, v_val_4200_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
return v___x_4201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4202_, lean_object* v_binders_4203_, lean_object* v_docString_x3f_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_addDocString_x27(v_declName_4202_, v_binders_4203_, v_docString_x3f_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_);
lean_dec(v_a_4210_);
lean_dec_ref(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; lean_object* v_nextMacroScope_4218_; lean_object* v_ngen_4219_; lean_object* v_auxDeclNGen_4220_; lean_object* v_traceState_4221_; lean_object* v_messages_4222_; lean_object* v_infoState_4223_; lean_object* v_snapshotTasks_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4250_; 
v___x_4217_ = lean_st_ref_take(v___y_4215_);
v_nextMacroScope_4218_ = lean_ctor_get(v___x_4217_, 1);
v_ngen_4219_ = lean_ctor_get(v___x_4217_, 2);
v_auxDeclNGen_4220_ = lean_ctor_get(v___x_4217_, 3);
v_traceState_4221_ = lean_ctor_get(v___x_4217_, 4);
v_messages_4222_ = lean_ctor_get(v___x_4217_, 6);
v_infoState_4223_ = lean_ctor_get(v___x_4217_, 7);
v_snapshotTasks_4224_ = lean_ctor_get(v___x_4217_, 8);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; lean_object* v_unused_4252_; 
v_unused_4251_ = lean_ctor_get(v___x_4217_, 5);
lean_dec(v_unused_4251_);
v_unused_4252_ = lean_ctor_get(v___x_4217_, 0);
lean_dec(v_unused_4252_);
v___x_4226_ = v___x_4217_;
v_isShared_4227_ = v_isSharedCheck_4250_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_snapshotTasks_4224_);
lean_inc(v_infoState_4223_);
lean_inc(v_messages_4222_);
lean_inc(v_traceState_4221_);
lean_inc(v_auxDeclNGen_4220_);
lean_inc(v_ngen_4219_);
lean_inc(v_nextMacroScope_4218_);
lean_dec(v___x_4217_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4250_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4228_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 5, v___x_4228_);
lean_ctor_set(v___x_4226_, 0, v_env_4213_);
v___x_4230_ = v___x_4226_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_env_4213_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_nextMacroScope_4218_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v_ngen_4219_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_auxDeclNGen_4220_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v_traceState_4221_);
lean_ctor_set(v_reuseFailAlloc_4249_, 5, v___x_4228_);
lean_ctor_set(v_reuseFailAlloc_4249_, 6, v_messages_4222_);
lean_ctor_set(v_reuseFailAlloc_4249_, 7, v_infoState_4223_);
lean_ctor_set(v_reuseFailAlloc_4249_, 8, v_snapshotTasks_4224_);
v___x_4230_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v_mctx_4233_; lean_object* v_zetaDeltaFVarIds_4234_; lean_object* v_postponed_4235_; lean_object* v_diag_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4247_; 
v___x_4231_ = lean_st_ref_put(v___y_4215_, v___x_4230_);
v___x_4232_ = lean_st_ref_take(v___y_4214_);
v_mctx_4233_ = lean_ctor_get(v___x_4232_, 0);
v_zetaDeltaFVarIds_4234_ = lean_ctor_get(v___x_4232_, 2);
v_postponed_4235_ = lean_ctor_get(v___x_4232_, 3);
v_diag_4236_ = lean_ctor_get(v___x_4232_, 4);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4247_ == 0)
{
lean_object* v_unused_4248_; 
v_unused_4248_ = lean_ctor_get(v___x_4232_, 1);
lean_dec(v_unused_4248_);
v___x_4238_ = v___x_4232_;
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_diag_4236_);
lean_inc(v_postponed_4235_);
lean_inc(v_zetaDeltaFVarIds_4234_);
lean_inc(v_mctx_4233_);
lean_dec(v___x_4232_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4247_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4240_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 1, v___x_4240_);
v___x_4242_ = v___x_4238_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_mctx_4233_);
lean_ctor_set(v_reuseFailAlloc_4246_, 1, v___x_4240_);
lean_ctor_set(v_reuseFailAlloc_4246_, 2, v_zetaDeltaFVarIds_4234_);
lean_ctor_set(v_reuseFailAlloc_4246_, 3, v_postponed_4235_);
lean_ctor_set(v_reuseFailAlloc_4246_, 4, v_diag_4236_);
v___x_4242_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4243_ = lean_st_ref_put(v___y_4214_, v___x_4242_);
v___x_4244_ = lean_box(0);
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4244_);
return v___x_4245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec(v___y_4254_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4258_, lean_object* v_as_4259_, size_t v_i_4260_, size_t v_stop_4261_, lean_object* v_b_4262_){
_start:
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_usize_dec_eq(v_i_4260_, v_stop_4261_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v_index_4265_; lean_object* v_sourceString_4266_; lean_object* v_imports_4267_; lean_object* v_currNamespace_4268_; lean_object* v_openDecls_4269_; lean_object* v_options_4270_; lean_object* v_check_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4287_; 
v___x_4264_ = lean_array_uget(v_as_4259_, v_i_4260_);
v_index_4265_ = lean_ctor_get(v___x_4264_, 1);
v_sourceString_4266_ = lean_ctor_get(v___x_4264_, 2);
v_imports_4267_ = lean_ctor_get(v___x_4264_, 3);
v_currNamespace_4268_ = lean_ctor_get(v___x_4264_, 4);
v_openDecls_4269_ = lean_ctor_get(v___x_4264_, 5);
v_options_4270_ = lean_ctor_get(v___x_4264_, 6);
v_check_4271_ = lean_ctor_get(v___x_4264_, 7);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; 
v_unused_4288_ = lean_ctor_get(v___x_4264_, 0);
lean_dec(v_unused_4288_);
v___x_4273_ = v___x_4264_;
v_isShared_4274_ = v_isSharedCheck_4287_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_check_4271_);
lean_inc(v_options_4270_);
lean_inc(v_openDecls_4269_);
lean_inc(v_currNamespace_4268_);
lean_inc(v_imports_4267_);
lean_inc(v_sourceString_4266_);
lean_inc(v_index_4265_);
lean_dec(v___x_4264_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4287_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4275_; lean_object* v_toEnvExtension_4276_; lean_object* v_asyncMode_4277_; lean_object* v___x_4278_; lean_object* v___x_4280_; 
v___x_4275_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4276_ = lean_ctor_get(v___x_4275_, 0);
v_asyncMode_4277_ = lean_ctor_get(v_toEnvExtension_4276_, 2);
lean_inc(v_n_4258_);
v___x_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4278_, 0, v_n_4258_);
if (v_isShared_4274_ == 0)
{
lean_ctor_set(v___x_4273_, 0, v___x_4278_);
v___x_4280_ = v___x_4273_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v___x_4278_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_index_4265_);
lean_ctor_set(v_reuseFailAlloc_4286_, 2, v_sourceString_4266_);
lean_ctor_set(v_reuseFailAlloc_4286_, 3, v_imports_4267_);
lean_ctor_set(v_reuseFailAlloc_4286_, 4, v_currNamespace_4268_);
lean_ctor_set(v_reuseFailAlloc_4286_, 5, v_openDecls_4269_);
lean_ctor_set(v_reuseFailAlloc_4286_, 6, v_options_4270_);
lean_ctor_set(v_reuseFailAlloc_4286_, 7, v_check_4271_);
v___x_4280_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; size_t v___x_4283_; size_t v___x_4284_; 
v___x_4281_ = lean_box(0);
v___x_4282_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4275_, v_b_4262_, v___x_4280_, v_asyncMode_4277_, v___x_4281_);
v___x_4283_ = ((size_t)1ULL);
v___x_4284_ = lean_usize_add(v_i_4260_, v___x_4283_);
v_i_4260_ = v___x_4284_;
v_b_4262_ = v___x_4282_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4258_);
return v_b_4262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4289_, lean_object* v_as_4290_, lean_object* v_i_4291_, lean_object* v_stop_4292_, lean_object* v_b_4293_){
_start:
{
size_t v_i_boxed_4294_; size_t v_stop_boxed_4295_; lean_object* v_res_4296_; 
v_i_boxed_4294_ = lean_unbox_usize(v_i_4291_);
lean_dec(v_i_4291_);
v_stop_boxed_4295_ = lean_unbox_usize(v_stop_4292_);
lean_dec(v_stop_4292_);
v_res_4296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4289_, v_as_4290_, v_i_boxed_4294_, v_stop_boxed_4295_, v_b_4293_);
lean_dec_ref(v_as_4290_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4297_, lean_object* v_deferred_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v___x_4306_; lean_object* v_env_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4306_ = lean_st_ref_get(v___y_4304_);
v_env_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc_ref(v_env_4307_);
lean_dec(v___x_4306_);
v___x_4308_ = l_Lean_getMainModuleDoc(v_env_4307_);
v___x_4309_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4308_);
lean_dec_ref(v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
lean_dec_ref(v_docs_4297_);
v___x_4310_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4311_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4310_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4311_;
}
else
{
lean_object* v___x_4312_; lean_object* v_env_4313_; lean_object* v___x_4314_; lean_object* v_size_4315_; lean_object* v___x_4316_; lean_object* v_env_4317_; lean_object* v___x_4318_; 
v___x_4312_ = lean_st_ref_get(v___y_4304_);
v_env_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc_ref(v_env_4313_);
lean_dec(v___x_4312_);
v___x_4314_ = l_Lean_getMainVersoModuleDocs(v_env_4313_);
v_size_4315_ = lean_ctor_get(v___x_4314_, 2);
lean_inc(v_size_4315_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = lean_st_ref_get(v___y_4304_);
v_env_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc_ref(v_env_4317_);
lean_dec(v___x_4316_);
v___x_4318_ = l_Lean_addVersoModuleDocSnippet(v_env_4317_, v_docs_4297_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
lean_dec(v_size_4315_);
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4321_ = l_Lean_stringToMessageData(v_a_4319_);
v___x_4322_ = l_Lean_indentD(v___x_4321_);
v___x_4323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4320_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4323_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
return v___x_4324_;
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; 
v_a_4325_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4326_ = lean_unsigned_to_nat(0u);
v___x_4327_ = lean_array_get_size(v_deferred_4298_);
v___x_4328_ = lean_nat_dec_lt(v___x_4326_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; 
lean_dec(v_size_4315_);
v___x_4329_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4325_, v___y_4302_, v___y_4304_);
return v___x_4329_;
}
else
{
size_t v___x_4330_; size_t v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4330_ = ((size_t)0ULL);
v___x_4331_ = lean_usize_of_nat(v___x_4327_);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4315_, v_deferred_4298_, v___x_4330_, v___x_4331_, v_a_4325_);
v___x_4333_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4332_, v___y_4302_, v___y_4304_);
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4334_, lean_object* v_deferred_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4334_, v_deferred_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec_ref(v_deferred_4335_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4344_, lean_object* v_docComment_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_versoModDocString(v_range_4344_, v_docComment_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v_fst_4355_; lean_object* v_snd_4356_; lean_object* v___x_4357_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v_fst_4355_ = lean_ctor_get(v_a_4354_, 0);
lean_inc(v_fst_4355_);
v_snd_4356_ = lean_ctor_get(v_a_4354_, 1);
lean_inc(v_snd_4356_);
lean_dec(v_a_4354_);
v___x_4357_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4355_, v_snd_4356_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_snd_4356_);
return v___x_4357_;
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
v_a_4358_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4353_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4353_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4366_, lean_object* v_docComment_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_addVersoModDocString(v_range_4366_, v_docComment_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_docComment_4367_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4376_, v___y_4380_, v___y_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
return v_res_4393_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Term_TermElabM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
