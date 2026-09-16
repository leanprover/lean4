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
lean_object* v_val_826_; lean_object* v_fileName_827_; lean_object* v_options_828_; lean_object* v_currRecDepth_829_; lean_object* v_maxRecDepth_830_; lean_object* v_ref_831_; lean_object* v_currNamespace_832_; lean_object* v_openDecls_833_; lean_object* v_initHeartbeats_834_; lean_object* v_maxHeartbeats_835_; lean_object* v_quotContext_836_; lean_object* v_currMacroScope_837_; uint8_t v_diag_838_; lean_object* v_cancelTk_x3f_839_; uint8_t v_suppressElabErrors_840_; lean_object* v_inheritedTraceOptions_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_val_826_ = lean_ctor_get(v_fileMap_x3f_813_, 0);
v_fileName_827_ = lean_ctor_get(v___y_822_, 0);
v_options_828_ = lean_ctor_get(v___y_822_, 2);
v_currRecDepth_829_ = lean_ctor_get(v___y_822_, 3);
v_maxRecDepth_830_ = lean_ctor_get(v___y_822_, 4);
v_ref_831_ = lean_ctor_get(v___y_822_, 5);
v_currNamespace_832_ = lean_ctor_get(v___y_822_, 6);
v_openDecls_833_ = lean_ctor_get(v___y_822_, 7);
v_initHeartbeats_834_ = lean_ctor_get(v___y_822_, 8);
v_maxHeartbeats_835_ = lean_ctor_get(v___y_822_, 9);
v_quotContext_836_ = lean_ctor_get(v___y_822_, 10);
v_currMacroScope_837_ = lean_ctor_get(v___y_822_, 11);
v_diag_838_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*14);
v_cancelTk_x3f_839_ = lean_ctor_get(v___y_822_, 12);
v_suppressElabErrors_840_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_841_ = lean_ctor_get(v___y_822_, 13);
lean_inc_ref(v_inheritedTraceOptions_841_);
lean_inc(v_cancelTk_x3f_839_);
lean_inc(v_currMacroScope_837_);
lean_inc(v_quotContext_836_);
lean_inc(v_maxHeartbeats_835_);
lean_inc(v_initHeartbeats_834_);
lean_inc(v_openDecls_833_);
lean_inc(v_currNamespace_832_);
lean_inc(v_ref_831_);
lean_inc(v_maxRecDepth_830_);
lean_inc(v_currRecDepth_829_);
lean_inc_ref(v_options_828_);
lean_inc(v_val_826_);
lean_inc_ref(v_fileName_827_);
v___x_842_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_842_, 0, v_fileName_827_);
lean_ctor_set(v___x_842_, 1, v_val_826_);
lean_ctor_set(v___x_842_, 2, v_options_828_);
lean_ctor_set(v___x_842_, 3, v_currRecDepth_829_);
lean_ctor_set(v___x_842_, 4, v_maxRecDepth_830_);
lean_ctor_set(v___x_842_, 5, v_ref_831_);
lean_ctor_set(v___x_842_, 6, v_currNamespace_832_);
lean_ctor_set(v___x_842_, 7, v_openDecls_833_);
lean_ctor_set(v___x_842_, 8, v_initHeartbeats_834_);
lean_ctor_set(v___x_842_, 9, v_maxHeartbeats_835_);
lean_ctor_set(v___x_842_, 10, v_quotContext_836_);
lean_ctor_set(v___x_842_, 11, v_currMacroScope_837_);
lean_ctor_set(v___x_842_, 12, v_cancelTk_x3f_839_);
lean_ctor_set(v___x_842_, 13, v_inheritedTraceOptions_841_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*14, v_diag_838_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*14 + 1, v_suppressElabErrors_840_);
v___x_843_ = l_Lean_Doc_DocM_exec___redArg(v_declName_814_, v_binders_815_, v___x_816_, v___x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___x_842_, v___y_823_);
lean_dec_ref_known(v___x_842_, 14);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_844_, lean_object* v_declName_845_, lean_object* v_binders_846_, lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
uint8_t v___x_9684__boxed_856_; lean_object* v_res_857_; 
v___x_9684__boxed_856_ = lean_unbox(v___x_848_);
v_res_857_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_844_, v_declName_845_, v_binders_846_, v___x_847_, v___x_9684__boxed_856_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v_fileMap_x3f_844_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_861_ == 0)
{
return v_bs_860_;
}
else
{
lean_object* v_v_862_; lean_object* v___x_863_; lean_object* v_bs_x27_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v_v_862_ = lean_array_uget(v_bs_860_, v_i_859_);
v___x_863_ = lean_unsigned_to_nat(0u);
v_bs_x27_864_ = lean_array_uset(v_bs_860_, v_i_859_, v___x_863_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_859_, v___x_865_);
v___x_867_ = lean_array_uset(v_bs_x27_864_, v_i_859_, v_v_862_);
v_i_859_ = v___x_866_;
v_bs_860_ = v___x_867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_bs_871_){
_start:
{
size_t v_sz_boxed_872_; size_t v_i_boxed_873_; lean_object* v_res_874_; 
v_sz_boxed_872_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_873_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_872_, v_i_boxed_873_, v_bs_871_);
return v_res_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_875_, lean_object* v_opt_876_){
_start:
{
lean_object* v_name_877_; lean_object* v_defValue_878_; lean_object* v_map_879_; lean_object* v___x_880_; 
v_name_877_ = lean_ctor_get(v_opt_876_, 0);
v_defValue_878_ = lean_ctor_get(v_opt_876_, 1);
v_map_879_ = lean_ctor_get(v_opts_875_, 0);
v___x_880_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_879_, v_name_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
uint8_t v___x_881_; 
v___x_881_ = lean_unbox(v_defValue_878_);
return v___x_881_;
}
else
{
lean_object* v_val_882_; 
v_val_882_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_880_, 1);
if (lean_obj_tag(v_val_882_) == 1)
{
uint8_t v_v_883_; 
v_v_883_ = lean_ctor_get_uint8(v_val_882_, 0);
lean_dec_ref_known(v_val_882_, 0);
return v_v_883_;
}
else
{
uint8_t v___x_884_; 
lean_dec(v_val_882_);
v___x_884_ = lean_unbox(v_defValue_878_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_885_, lean_object* v_opt_886_){
_start:
{
uint8_t v_res_887_; lean_object* v_r_888_; 
v_res_887_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_885_, v_opt_886_);
lean_dec_ref(v_opt_886_);
lean_dec_ref(v_opts_885_);
v_r_888_ = lean_box(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_env_896_; lean_object* v___x_897_; lean_object* v_mctx_898_; lean_object* v_lctx_899_; lean_object* v_options_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_895_ = lean_st_ref_get(v___y_893_);
v_env_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc_ref(v_env_896_);
lean_dec(v___x_895_);
v___x_897_ = lean_st_ref_get(v___y_891_);
v_mctx_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_mctx_898_);
lean_dec(v___x_897_);
v_lctx_899_ = lean_ctor_get(v___y_890_, 2);
v_options_900_ = lean_ctor_get(v___y_892_, 2);
lean_inc_ref(v_options_900_);
lean_inc_ref(v_lctx_899_);
v___x_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_901_, 0, v_env_896_);
lean_ctor_set(v___x_901_, 1, v_mctx_898_);
lean_ctor_set(v___x_901_, 2, v_lctx_899_);
lean_ctor_set(v___x_901_, 3, v_options_900_);
v___x_902_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_msgData_889_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_919_, uint8_t v___y_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_921_) == 1)
{
lean_object* v_pre_922_; 
v_pre_922_ = lean_ctor_get(v_x_921_, 0);
switch(lean_obj_tag(v_pre_922_))
{
case 1:
{
lean_object* v_pre_923_; 
v_pre_923_ = lean_ctor_get(v_pre_922_, 0);
switch(lean_obj_tag(v_pre_923_))
{
case 0:
{
lean_object* v_str_924_; lean_object* v_str_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_str_924_ = lean_ctor_get(v_x_921_, 1);
v_str_925_ = lean_ctor_get(v_pre_922_, 1);
v___x_926_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_927_ = lean_string_dec_eq(v_str_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_929_ = lean_string_dec_eq(v_str_925_, v___x_928_);
if (v___x_929_ == 0)
{
return v___x_929_;
}
else
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_931_ = lean_string_dec_eq(v_str_924_, v___x_930_);
if (v___x_931_ == 0)
{
return v___x_931_;
}
else
{
return v_suppressElabErrors_919_;
}
}
}
else
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_933_ = lean_string_dec_eq(v_str_924_, v___x_932_);
if (v___x_933_ == 0)
{
return v___x_933_;
}
else
{
return v_suppressElabErrors_919_;
}
}
}
case 1:
{
lean_object* v_pre_934_; 
v_pre_934_ = lean_ctor_get(v_pre_923_, 0);
if (lean_obj_tag(v_pre_934_) == 0)
{
lean_object* v_str_935_; lean_object* v_str_936_; lean_object* v_str_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_str_935_ = lean_ctor_get(v_x_921_, 1);
v_str_936_ = lean_ctor_get(v_pre_922_, 1);
v_str_937_ = lean_ctor_get(v_pre_923_, 1);
v___x_938_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_939_ = lean_string_dec_eq(v_str_937_, v___x_938_);
if (v___x_939_ == 0)
{
return v___x_939_;
}
else
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_941_ = lean_string_dec_eq(v_str_936_, v___x_940_);
if (v___x_941_ == 0)
{
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_943_ = lean_string_dec_eq(v_str_935_, v___x_942_);
if (v___x_943_ == 0)
{
return v___x_943_;
}
else
{
return v_suppressElabErrors_919_;
}
}
}
}
else
{
return v___y_920_;
}
}
default: 
{
return v___y_920_;
}
}
}
case 0:
{
lean_object* v_str_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_str_944_ = lean_ctor_get(v_x_921_, 1);
v___x_945_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_946_ = lean_string_dec_eq(v_str_944_, v___x_945_);
if (v___x_946_ == 0)
{
return v___x_946_;
}
else
{
return v_suppressElabErrors_919_;
}
}
default: 
{
return v___y_920_;
}
}
}
else
{
return v___y_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_947_, lean_object* v___y_948_, lean_object* v_x_949_){
_start:
{
uint8_t v_suppressElabErrors_boxed_950_; uint8_t v___y_9781__boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v_suppressElabErrors_boxed_950_ = lean_unbox(v_suppressElabErrors_947_);
v___y_9781__boxed_951_ = lean_unbox(v___y_948_);
v_res_952_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_950_, v___y_9781__boxed_951_, v_x_949_);
lean_dec(v_x_949_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_954_, lean_object* v_msgData_955_, uint8_t v_severity_956_, uint8_t v_isSilent_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___y_964_; lean_object* v___y_965_; uint8_t v___y_966_; lean_object* v___y_967_; uint8_t v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_1000_; lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1003_; uint8_t v___y_1004_; uint8_t v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1025_; lean_object* v___y_1026_; uint8_t v___y_1027_; uint8_t v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; lean_object* v___y_1041_; uint8_t v___y_1042_; uint8_t v___x_1047_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; uint8_t v___y_1055_; uint8_t v___y_1057_; uint8_t v___x_1072_; 
v___x_1047_ = 2;
v___x_1072_ = l_Lean_instBEqMessageSeverity_beq(v_severity_956_, v___x_1047_);
if (v___x_1072_ == 0)
{
v___y_1057_ = v___x_1072_;
goto v___jp_1056_;
}
else
{
uint8_t v___x_1073_; 
lean_inc_ref(v_msgData_955_);
v___x_1073_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_955_);
v___y_1057_ = v___x_1073_;
goto v___jp_1056_;
}
v___jp_963_:
{
lean_object* v___x_973_; lean_object* v_currNamespace_974_; lean_object* v_openDecls_975_; lean_object* v_env_976_; lean_object* v_nextMacroScope_977_; lean_object* v_ngen_978_; lean_object* v_auxDeclNGen_979_; lean_object* v_traceState_980_; lean_object* v_cache_981_; lean_object* v_messages_982_; lean_object* v_infoState_983_; lean_object* v_snapshotTasks_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_998_; 
v___x_973_ = lean_st_ref_take(v___y_972_);
v_currNamespace_974_ = lean_ctor_get(v___y_971_, 6);
v_openDecls_975_ = lean_ctor_get(v___y_971_, 7);
v_env_976_ = lean_ctor_get(v___x_973_, 0);
v_nextMacroScope_977_ = lean_ctor_get(v___x_973_, 1);
v_ngen_978_ = lean_ctor_get(v___x_973_, 2);
v_auxDeclNGen_979_ = lean_ctor_get(v___x_973_, 3);
v_traceState_980_ = lean_ctor_get(v___x_973_, 4);
v_cache_981_ = lean_ctor_get(v___x_973_, 5);
v_messages_982_ = lean_ctor_get(v___x_973_, 6);
v_infoState_983_ = lean_ctor_get(v___x_973_, 7);
v_snapshotTasks_984_ = lean_ctor_get(v___x_973_, 8);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_998_ == 0)
{
v___x_986_ = v___x_973_;
v_isShared_987_ = v_isSharedCheck_998_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snapshotTasks_984_);
lean_inc(v_infoState_983_);
lean_inc(v_messages_982_);
lean_inc(v_cache_981_);
lean_inc(v_traceState_980_);
lean_inc(v_auxDeclNGen_979_);
lean_inc(v_ngen_978_);
lean_inc(v_nextMacroScope_977_);
lean_inc(v_env_976_);
lean_dec(v___x_973_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_998_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
lean_inc(v_openDecls_975_);
lean_inc(v_currNamespace_974_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_currNamespace_974_);
lean_ctor_set(v___x_988_, 1, v_openDecls_975_);
v___x_989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc_ref(v___y_970_);
v___x_990_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_990_, 0, v___y_970_);
lean_ctor_set(v___x_990_, 1, v___y_967_);
lean_ctor_set(v___x_990_, 2, v___y_969_);
lean_ctor_set(v___x_990_, 3, v___y_964_);
lean_ctor_set(v___x_990_, 4, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*5, v___y_966_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*5 + 1, v___y_968_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*5 + 2, v_isSilent_957_);
v___x_991_ = l_Lean_MessageLog_add(v___x_990_, v_messages_982_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 6, v___x_991_);
v___x_993_ = v___x_986_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_env_976_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_978_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_979_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_traceState_980_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_cache_981_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_infoState_983_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_snapshotTasks_984_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_st_ref_put(v___y_972_, v___x_993_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
v___jp_999_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1023_; 
v___x_1008_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_955_);
v___x_1009_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_1008_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1023_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_inc_ref_n(v___y_1003_, 2);
v___x_1014_ = l_Lean_FileMap_toPosition(v___y_1003_, v___y_1001_);
lean_dec(v___y_1001_);
v___x_1015_ = l_Lean_FileMap_toPosition(v___y_1003_, v___y_1007_);
lean_dec(v___y_1007_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1005_ == 0)
{
lean_del_object(v___x_1012_);
lean_dec_ref(v___y_1000_);
v___y_964_ = v___x_1017_;
v___y_965_ = v_a_1010_;
v___y_966_ = v___y_1002_;
v___y_967_ = v___x_1014_;
v___y_968_ = v___y_1004_;
v___y_969_ = v___x_1016_;
v___y_970_ = v___y_1006_;
v___y_971_ = v___y_960_;
v___y_972_ = v___y_961_;
goto v___jp_963_;
}
else
{
uint8_t v___x_1018_; 
lean_inc(v_a_1010_);
v___x_1018_ = l_Lean_MessageData_hasTag(v___y_1000_, v_a_1010_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
lean_dec_ref_known(v___x_1016_, 1);
lean_dec_ref(v___x_1014_);
lean_dec(v_a_1010_);
v___x_1019_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1019_);
v___x_1021_ = v___x_1012_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
else
{
lean_del_object(v___x_1012_);
v___y_964_ = v___x_1017_;
v___y_965_ = v_a_1010_;
v___y_966_ = v___y_1002_;
v___y_967_ = v___x_1014_;
v___y_968_ = v___y_1004_;
v___y_969_ = v___x_1016_;
v___y_970_ = v___y_1006_;
v___y_971_ = v___y_960_;
v___y_972_ = v___y_961_;
goto v___jp_963_;
}
}
}
}
v___jp_1024_:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Syntax_getTailPos_x3f(v___y_1031_, v___y_1027_);
lean_dec(v___y_1031_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_inc(v___y_1032_);
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1032_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___y_1026_;
v___y_1004_ = v___y_1028_;
v___y_1005_ = v___y_1029_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v___y_1032_;
goto v___jp_999_;
}
else
{
lean_object* v_val_1034_; 
v_val_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_val_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___y_1000_ = v___y_1025_;
v___y_1001_ = v___y_1032_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___y_1026_;
v___y_1004_ = v___y_1028_;
v___y_1005_ = v___y_1029_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v_val_1034_;
goto v___jp_999_;
}
}
v___jp_1035_:
{
lean_object* v_ref_1043_; lean_object* v___x_1044_; 
v_ref_1043_ = l_Lean_replaceRef(v_ref_954_, v___y_1039_);
v___x_1044_ = l_Lean_Syntax_getPos_x3f(v_ref_1043_, v___y_1037_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___y_1025_ = v___y_1036_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1037_;
v___y_1028_ = v___y_1042_;
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1041_;
v___y_1031_ = v_ref_1043_;
v___y_1032_ = v___x_1045_;
goto v___jp_1024_;
}
else
{
lean_object* v_val_1046_; 
v_val_1046_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v___x_1044_, 1);
v___y_1025_ = v___y_1036_;
v___y_1026_ = v___y_1038_;
v___y_1027_ = v___y_1037_;
v___y_1028_ = v___y_1042_;
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1041_;
v___y_1031_ = v_ref_1043_;
v___y_1032_ = v_val_1046_;
goto v___jp_1024_;
}
}
v___jp_1048_:
{
if (v___y_1055_ == 0)
{
v___y_1036_ = v___y_1050_;
v___y_1037_ = v___y_1054_;
v___y_1038_ = v___y_1049_;
v___y_1039_ = v___y_1051_;
v___y_1040_ = v___y_1052_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v_severity_956_;
goto v___jp_1035_;
}
else
{
v___y_1036_ = v___y_1050_;
v___y_1037_ = v___y_1054_;
v___y_1038_ = v___y_1049_;
v___y_1039_ = v___y_1051_;
v___y_1040_ = v___y_1052_;
v___y_1041_ = v___y_1053_;
v___y_1042_ = v___x_1047_;
goto v___jp_1035_;
}
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
lean_object* v_fileName_1058_; lean_object* v_fileMap_1059_; lean_object* v_options_1060_; lean_object* v_ref_1061_; uint8_t v_suppressElabErrors_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___f_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; 
v_fileName_1058_ = lean_ctor_get(v___y_960_, 0);
v_fileMap_1059_ = lean_ctor_get(v___y_960_, 1);
v_options_1060_ = lean_ctor_get(v___y_960_, 2);
v_ref_1061_ = lean_ctor_get(v___y_960_, 5);
v_suppressElabErrors_1062_ = lean_ctor_get_uint8(v___y_960_, sizeof(void*)*14 + 1);
v___x_1063_ = lean_box(v_suppressElabErrors_1062_);
v___x_1064_ = lean_box(v___y_1057_);
v___f_1065_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1065_, 0, v___x_1063_);
lean_closure_set(v___f_1065_, 1, v___x_1064_);
v___x_1066_ = 1;
v___x_1067_ = l_Lean_instBEqMessageSeverity_beq(v_severity_956_, v___x_1066_);
if (v___x_1067_ == 0)
{
v___y_1049_ = v_fileMap_1059_;
v___y_1050_ = v___f_1065_;
v___y_1051_ = v_ref_1061_;
v___y_1052_ = v_suppressElabErrors_1062_;
v___y_1053_ = v_fileName_1058_;
v___y_1054_ = v___y_1057_;
v___y_1055_ = v___x_1067_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = l_Lean_warningAsError;
v___x_1069_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1060_, v___x_1068_);
v___y_1049_ = v_fileMap_1059_;
v___y_1050_ = v___f_1065_;
v___y_1051_ = v_ref_1061_;
v___y_1052_ = v_suppressElabErrors_1062_;
v___y_1053_ = v_fileName_1058_;
v___y_1054_ = v___y_1057_;
v___y_1055_ = v___x_1069_;
goto v___jp_1048_;
}
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec_ref(v_msgData_955_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1074_, lean_object* v_msgData_1075_, lean_object* v_severity_1076_, lean_object* v_isSilent_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
uint8_t v_severity_boxed_1083_; uint8_t v_isSilent_boxed_1084_; lean_object* v_res_1085_; 
v_severity_boxed_1083_ = lean_unbox(v_severity_1076_);
v_isSilent_boxed_1084_ = lean_unbox(v_isSilent_1077_);
v_res_1085_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1074_, v_msgData_1075_, v_severity_boxed_1083_, v_isSilent_boxed_1084_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v_ref_1074_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1086_, size_t v_sz_1087_, size_t v_i_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_usize_dec_lt(v_i_1088_, v_sz_1087_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_b_1089_);
return v___x_1098_;
}
else
{
lean_object* v_ref_1099_; lean_object* v_a_1100_; uint8_t v_severity_1101_; uint8_t v_isSilent_1102_; lean_object* v_data_1103_; lean_object* v___x_1104_; 
v_ref_1099_ = lean_ctor_get(v___y_1094_, 5);
v_a_1100_ = lean_array_uget_borrowed(v_as_1086_, v_i_1088_);
v_severity_1101_ = lean_ctor_get_uint8(v_a_1100_, sizeof(void*)*5 + 1);
v_isSilent_1102_ = lean_ctor_get_uint8(v_a_1100_, sizeof(void*)*5 + 2);
v_data_1103_ = lean_ctor_get(v_a_1100_, 4);
lean_inc(v_data_1103_);
v___x_1104_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1099_, v_data_1103_, v_severity_1101_, v_isSilent_1102_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; 
lean_dec_ref_known(v___x_1104_, 1);
v___x_1105_ = lean_box(0);
v___x_1106_ = ((size_t)1ULL);
v___x_1107_ = lean_usize_add(v_i_1088_, v___x_1106_);
v_i_1088_ = v___x_1107_;
v_b_1089_ = v___x_1105_;
goto _start;
}
else
{
return v___x_1104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1109_, lean_object* v_sz_1110_, lean_object* v_i_1111_, lean_object* v_b_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
size_t v_sz_boxed_1120_; size_t v_i_boxed_1121_; lean_object* v_res_1122_; 
v_sz_boxed_1120_ = lean_unbox_usize(v_sz_1110_);
lean_dec(v_sz_1110_);
v_i_boxed_1121_ = lean_unbox_usize(v_i_1111_);
lean_dec(v_i_1111_);
v_res_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1109_, v_sz_boxed_1120_, v_i_boxed_1121_, v_b_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec_ref(v_as_1109_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v_infoState_1127_; lean_object* v_env_1128_; lean_object* v_nextMacroScope_1129_; lean_object* v_ngen_1130_; lean_object* v_auxDeclNGen_1131_; lean_object* v_traceState_1132_; lean_object* v_cache_1133_; lean_object* v_messages_1134_; lean_object* v_snapshotTasks_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1155_; 
v___x_1126_ = lean_st_ref_take(v___y_1124_);
v_infoState_1127_ = lean_ctor_get(v___x_1126_, 7);
v_env_1128_ = lean_ctor_get(v___x_1126_, 0);
v_nextMacroScope_1129_ = lean_ctor_get(v___x_1126_, 1);
v_ngen_1130_ = lean_ctor_get(v___x_1126_, 2);
v_auxDeclNGen_1131_ = lean_ctor_get(v___x_1126_, 3);
v_traceState_1132_ = lean_ctor_get(v___x_1126_, 4);
v_cache_1133_ = lean_ctor_get(v___x_1126_, 5);
v_messages_1134_ = lean_ctor_get(v___x_1126_, 6);
v_snapshotTasks_1135_ = lean_ctor_get(v___x_1126_, 8);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snapshotTasks_1135_);
lean_inc(v_infoState_1127_);
lean_inc(v_messages_1134_);
lean_inc(v_cache_1133_);
lean_inc(v_traceState_1132_);
lean_inc(v_auxDeclNGen_1131_);
lean_inc(v_ngen_1130_);
lean_inc(v_nextMacroScope_1129_);
lean_inc(v_env_1128_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1155_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_assignment_1139_; lean_object* v_lazyAssignment_1140_; lean_object* v_trees_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_assignment_1139_ = lean_ctor_get(v_infoState_1127_, 0);
v_lazyAssignment_1140_ = lean_ctor_get(v_infoState_1127_, 1);
v_trees_1141_ = lean_ctor_get(v_infoState_1127_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_infoState_1127_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1143_ = v_infoState_1127_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_trees_1141_);
lean_inc(v_lazyAssignment_1140_);
lean_inc(v_assignment_1139_);
lean_dec(v_infoState_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_assignment_1139_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_lazyAssignment_1140_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_trees_1141_);
v___x_1146_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
lean_ctor_set_uint8(v___x_1146_, sizeof(void*)*3, v_flag_1123_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 7, v___x_1146_);
v___x_1148_ = v___x_1137_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_env_1128_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_nextMacroScope_1129_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_ngen_1130_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_auxDeclNGen_1131_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_traceState_1132_);
lean_ctor_set(v_reuseFailAlloc_1152_, 5, v_cache_1133_);
lean_ctor_set(v_reuseFailAlloc_1152_, 6, v_messages_1134_);
lean_ctor_set(v_reuseFailAlloc_1152_, 7, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1152_, 8, v_snapshotTasks_1135_);
v___x_1148_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_st_ref_put(v___y_1124_, v___x_1148_);
v___x_1150_ = lean_box(0);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1150_);
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
uint8_t v_flag_boxed_1159_; lean_object* v_res_1160_; 
v_flag_boxed_1159_ = lean_unbox(v_flag_1156_);
v_res_1160_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1159_, v___y_1157_);
lean_dec(v___y_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v___x_1170_; lean_object* v_infoState_1171_; uint8_t v_enabled_1172_; lean_object* v_a_1174_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1170_ = lean_st_ref_get(v___y_1168_);
v_infoState_1171_ = lean_ctor_get(v___x_1170_, 7);
lean_inc_ref(v_infoState_1171_);
lean_dec(v___x_1170_);
v_enabled_1172_ = lean_ctor_get_uint8(v_infoState_1171_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1171_);
v___x_1184_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1161_, v___y_1168_);
lean_dec_ref(v___x_1184_);
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
lean_inc(v___y_1166_);
lean_inc_ref(v___y_1165_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1185_ = lean_apply_7(v_x_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, lean_box(0));
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v___x_1187_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1172_, v___y_1168_);
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
lean_ctor_set(v___x_1189_, 0, v_a_1186_);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_a_1196_; 
v_a_1196_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1185_, 1);
v_a_1174_ = v_a_1196_;
goto v___jp_1173_;
}
v___jp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v___x_1175_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1172_, v___y_1168_);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1175_, 0);
lean_dec(v_unused_1183_);
v___x_1177_ = v___x_1175_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v___x_1175_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
lean_ctor_set(v___x_1177_, 0, v_a_1174_);
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_flag_boxed_1206_; lean_object* v_res_1207_; 
v_flag_boxed_1206_ = lean_unbox(v_flag_1197_);
v_res_1207_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1206_, v_x_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1208_, lean_object* v_binders_1209_, lean_object* v_blocks_1210_, lean_object* v_fileMap_x3f_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v_a_1222_; size_t v_sz_1240_; size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___y_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v_sz_1240_ = lean_array_size(v_blocks_1210_);
v___x_1241_ = ((size_t)0ULL);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1240_, v___x_1241_, v_blocks_1210_);
v___x_1243_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = 1;
v___x_1245_ = lean_box(v___x_1244_);
v___y_1246_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1246_, 0, v_fileMap_x3f_1211_);
lean_closure_set(v___y_1246_, 1, v_declName_1208_);
lean_closure_set(v___y_1246_, 2, v_binders_1209_);
lean_closure_set(v___y_1246_, 3, v___x_1243_);
lean_closure_set(v___y_1246_, 4, v___x_1245_);
v___x_1247_ = 0;
v___x_1248_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1247_, v___y_1246_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v___x_1250_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1217_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1252_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v___x_1252_ = l_Lean_Core_setMessageLog___redArg(v_a_1220_, v_a_1217_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; size_t v_sz_1255_; lean_object* v___x_1256_; 
lean_dec_ref_known(v___x_1252_, 1);
v___x_1253_ = l_Lean_MessageLog_toArray(v_a_1251_);
lean_dec(v_a_1251_);
v___x_1254_ = lean_box(0);
v_sz_1255_ = lean_array_size(v___x_1253_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1253_, v_sz_1255_, v___x_1241_, v___x_1254_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
lean_dec_ref(v___x_1253_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1282_);
v___x_1258_ = v___x_1256_;
v_isShared_1259_ = v_isSharedCheck_1281_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1256_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1281_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1280_; 
v_fst_1260_ = lean_ctor_get(v_a_1249_, 0);
v_snd_1261_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1263_ = v_a_1249_;
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v_a_1249_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1280_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1279_; 
v_fst_1265_ = lean_ctor_get(v_fst_1260_, 0);
v_snd_1266_ = lean_ctor_get(v_fst_1260_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_fst_1260_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1268_ = v_fst_1260_;
v_isShared_1269_ = v_isSharedCheck_1279_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_fst_1260_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1279_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_fst_1265_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_snd_1266_);
v___x_1271_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1273_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1271_);
v___x_1273_ = v___x_1263_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1261_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1273_);
v___x_1275_ = v___x_1258_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
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
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v_a_1249_);
v_a_1283_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1256_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1256_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_a_1251_);
lean_dec(v_a_1249_);
v_a_1291_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1252_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1252_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; 
lean_dec(v_a_1249_);
v_a_1299_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1250_, 1);
v_a_1222_ = v_a_1299_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1300_; 
v_a_1300_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1248_, 1);
v_a_1222_ = v_a_1300_;
goto v___jp_1221_;
}
v___jp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_Core_setMessageLog___redArg(v_a_1220_, v_a_1217_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1231_);
v___x_1225_ = v___x_1223_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
lean_ctor_set(v___x_1225_, 0, v_a_1222_);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1222_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_a_1222_);
v_a_1232_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1223_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1223_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_fileMap_x3f_1211_);
lean_dec_ref(v_blocks_1210_);
lean_dec(v_binders_1209_);
lean_dec(v_declName_1208_);
v_a_1301_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1219_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1219_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1309_, lean_object* v_binders_1310_, lean_object* v_blocks_1311_, lean_object* v_fileMap_x3f_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1309_, v_binders_1310_, v_blocks_1311_, v_fileMap_x3f_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1321_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
uint8_t v_flag_boxed_1338_; lean_object* v_res_1339_; 
v_flag_boxed_1338_ = lean_unbox(v_flag_1330_);
v_res_1339_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1338_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1340_, uint8_t v_flag_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1341_, v_x_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_flag_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
uint8_t v_flag_boxed_1361_; lean_object* v_res_1362_; 
v_flag_boxed_1361_ = lean_unbox(v_flag_1352_);
v_res_1362_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1351_, v_flag_boxed_1361_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1363_, lean_object* v_msgData_1364_, uint8_t v_severity_1365_, uint8_t v_isSilent_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1363_, v_msgData_1364_, v_severity_1365_, v_isSilent_1366_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1375_, lean_object* v_msgData_1376_, lean_object* v_severity_1377_, lean_object* v_isSilent_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_severity_boxed_1386_; uint8_t v_isSilent_boxed_1387_; lean_object* v_res_1388_; 
v_severity_boxed_1386_ = lean_unbox(v_severity_1377_);
v_isSilent_boxed_1387_ = lean_unbox(v_isSilent_1378_);
v_res_1388_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1375_, v_msgData_1376_, v_severity_boxed_1386_, v_isSilent_boxed_1387_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_ref_1375_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1389_, uint8_t v_severity_1390_, uint8_t v_isSilent_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_ref_1397_; lean_object* v___x_1398_; 
v_ref_1397_ = lean_ctor_get(v___y_1394_, 5);
v___x_1398_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1397_, v_msgData_1389_, v_severity_1390_, v_isSilent_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1399_, lean_object* v_severity_1400_, lean_object* v_isSilent_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_severity_boxed_1407_; uint8_t v_isSilent_boxed_1408_; lean_object* v_res_1409_; 
v_severity_boxed_1407_ = lean_unbox(v_severity_1400_);
v_isSilent_boxed_1408_ = lean_unbox(v_isSilent_1401_);
v_res_1409_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1399_, v_severity_boxed_1407_, v_isSilent_boxed_1408_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = 2;
v___x_1419_ = 0;
v___x_1420_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1410_, v___x_1418_, v___x_1419_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1430_, size_t v_sz_1431_, size_t v_i_1432_, lean_object* v_b_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_usize_dec_lt(v_i_1432_, v_sz_1431_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1433_);
return v___x_1442_;
}
else
{
lean_object* v_a_1443_; lean_object* v_snd_1444_; lean_object* v_snd_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v_a_1443_ = lean_array_uget_borrowed(v_as_1430_, v_i_1432_);
v_snd_1444_ = lean_ctor_get(v_a_1443_, 1);
v_snd_1445_ = lean_ctor_get(v_snd_1444_, 1);
lean_inc(v_snd_1445_);
v___x_1446_ = l_Lean_Parser_Error_toString(v_snd_1445_);
v___x_1447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = l_Lean_MessageData_ofFormat(v___x_1447_);
v___x_1449_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1448_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; size_t v___x_1451_; size_t v___x_1452_; 
lean_dec_ref_known(v___x_1449_, 1);
v___x_1450_ = lean_box(0);
v___x_1451_ = ((size_t)1ULL);
v___x_1452_ = lean_usize_add(v_i_1432_, v___x_1451_);
v_i_1432_ = v___x_1452_;
v_b_1433_ = v___x_1450_;
goto _start;
}
else
{
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1454_, lean_object* v_sz_1455_, lean_object* v_i_1456_, lean_object* v_b_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
size_t v_sz_boxed_1465_; size_t v_i_boxed_1466_; lean_object* v_res_1467_; 
v_sz_boxed_1465_ = lean_unbox_usize(v_sz_1455_);
lean_dec(v_sz_1455_);
v_i_boxed_1466_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1454_, v_sz_boxed_1465_, v_i_boxed_1466_, v_b_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec_ref(v_as_1454_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1485_, lean_object* v_binders_1486_, lean_object* v_docComment_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_env_1496_; lean_object* v_fileName_1497_; lean_object* v_options_1498_; lean_object* v_currNamespace_1499_; lean_object* v_openDecls_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1495_ = lean_st_ref_get(v_a_1493_);
v_env_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc_ref_n(v_env_1496_, 2);
lean_dec(v___x_1495_);
v_fileName_1497_ = lean_ctor_get(v_a_1492_, 0);
v_options_1498_ = lean_ctor_get(v_a_1492_, 2);
v_currNamespace_1499_ = lean_ctor_get(v_a_1492_, 6);
v_openDecls_1500_ = lean_ctor_get(v_a_1492_, 7);
v___x_1501_ = lean_string_utf8_byte_size(v_docComment_1487_);
lean_inc_ref_n(v_docComment_1487_, 2);
v___x_1502_ = l_Lean_FileMap_ofString(v_docComment_1487_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v_fileName_1497_);
v___x_1503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1503_, 0, v_docComment_1487_);
lean_ctor_set(v___x_1503_, 1, v_fileName_1497_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
lean_ctor_set(v___x_1503_, 3, v___x_1501_);
lean_inc(v_openDecls_1500_);
lean_inc(v_currNamespace_1499_);
lean_inc_ref(v_options_1498_);
v___x_1504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1504_, 0, v_env_1496_);
lean_ctor_set(v___x_1504_, 1, v_options_1498_);
lean_ctor_set(v___x_1504_, 2, v_currNamespace_1499_);
lean_ctor_set(v___x_1504_, 3, v_openDecls_1500_);
v___x_1505_ = l_Lean_Parser_mkParserState(v_docComment_1487_);
lean_dec_ref(v_docComment_1487_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1508_ = l_Lean_Parser_getTokenTable(v_env_1496_);
v___x_1509_ = l_Lean_Parser_ParserFn_run(v___x_1507_, v___x_1503_, v___x_1504_, v___x_1508_, v___x_1505_);
lean_inc_ref(v___x_1509_);
v___x_1510_ = l_Lean_Parser_ParserState_allErrors(v___x_1509_);
v___x_1511_ = lean_array_get_size(v___x_1510_);
v___x_1512_ = lean_nat_dec_eq(v___x_1511_, v___x_1506_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; size_t v_sz_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
lean_dec_ref(v___x_1509_);
lean_dec_ref(v___x_1502_);
lean_dec(v_binders_1486_);
lean_dec(v_declName_1485_);
v___x_1513_ = lean_box(0);
v_sz_1514_ = lean_array_size(v___x_1510_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1510_, v_sz_1514_, v___x_1515_, v___x_1513_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec_ref(v___x_1510_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v___x_1516_, 0);
lean_dec(v_unused_1525_);
v___x_1518_ = v___x_1516_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v___x_1516_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1516_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1516_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_stxStack_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v___x_1510_);
v_stxStack_1534_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_stxStack_1534_);
lean_dec_ref(v___x_1509_);
v___x_1535_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1534_);
lean_dec_ref(v_stxStack_1534_);
v___x_1536_ = l_Lean_Syntax_getArgs(v___x_1535_);
lean_dec(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1502_);
v___x_1538_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1485_, v_binders_1486_, v___x_1536_, v___x_1537_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1539_, lean_object* v_binders_1540_, lean_object* v_docComment_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_versoDocStringOfText(v_declName_1539_, v_binders_1540_, v_docComment_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1550_, uint8_t v_severity_1551_, uint8_t v_isSilent_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1550_, v_severity_1551_, v_isSilent_1552_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1561_, lean_object* v_severity_1562_, lean_object* v_isSilent_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
uint8_t v_severity_boxed_1571_; uint8_t v_isSilent_boxed_1572_; lean_object* v_res_1573_; 
v_severity_boxed_1571_ = lean_unbox(v_severity_1562_);
v_isSilent_boxed_1572_ = lean_unbox(v_isSilent_1563_);
v_res_1573_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1561_, v_severity_boxed_1571_, v_isSilent_boxed_1572_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_1574_, size_t v_i_1575_, lean_object* v_bs_1576_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_lt(v_i_1575_, v_sz_1574_);
if (v___x_1577_ == 0)
{
return v_bs_1576_;
}
else
{
lean_object* v_v_1578_; lean_object* v___x_1579_; lean_object* v_bs_x27_1580_; size_t v___x_1581_; size_t v___x_1582_; lean_object* v___x_1583_; 
v_v_1578_ = lean_array_uget(v_bs_1576_, v_i_1575_);
v___x_1579_ = lean_unsigned_to_nat(0u);
v_bs_x27_1580_ = lean_array_uset(v_bs_1576_, v_i_1575_, v___x_1579_);
v___x_1581_ = ((size_t)1ULL);
v___x_1582_ = lean_usize_add(v_i_1575_, v___x_1581_);
v___x_1583_ = lean_array_uset(v_bs_x27_1580_, v_i_1575_, v_v_1578_);
v_i_1575_ = v___x_1582_;
v_bs_1576_ = v___x_1583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_1585_, lean_object* v_i_1586_, lean_object* v_bs_1587_){
_start:
{
size_t v_sz_boxed_1588_; size_t v_i_boxed_1589_; lean_object* v_res_1590_; 
v_sz_boxed_1588_ = lean_unbox_usize(v_sz_1585_);
lean_dec(v_sz_1585_);
v_i_boxed_1589_ = lean_unbox_usize(v_i_1586_);
lean_dec(v_i_1586_);
v_res_1590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_1588_, v_i_boxed_1589_, v_bs_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v_suppressElabErrors_1591_, uint8_t v___x_1592_, lean_object* v_x_1593_){
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
return v___x_1601_;
}
else
{
lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1603_ = lean_string_dec_eq(v_str_1596_, v___x_1602_);
if (v___x_1603_ == 0)
{
return v___x_1603_;
}
else
{
return v_suppressElabErrors_1591_;
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
return v___x_1605_;
}
else
{
return v_suppressElabErrors_1591_;
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
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1613_ = lean_string_dec_eq(v_str_1608_, v___x_1612_);
if (v___x_1613_ == 0)
{
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1615_ = lean_string_dec_eq(v_str_1607_, v___x_1614_);
if (v___x_1615_ == 0)
{
return v___x_1615_;
}
else
{
return v_suppressElabErrors_1591_;
}
}
}
}
else
{
return v___x_1592_;
}
}
default: 
{
return v___x_1592_;
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
return v___x_1618_;
}
else
{
return v_suppressElabErrors_1591_;
}
}
default: 
{
return v___x_1592_;
}
}
}
else
{
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1619_, lean_object* v___x_1620_, lean_object* v_x_1621_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1622_; uint8_t v___x_11397__boxed_1623_; uint8_t v_res_1624_; lean_object* v_r_1625_; 
v_suppressElabErrors_boxed_1622_ = lean_unbox(v_suppressElabErrors_1619_);
v___x_11397__boxed_1623_ = lean_unbox(v___x_1620_);
v_res_1624_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1622_, v___x_11397__boxed_1623_, v_x_1621_);
lean_dec(v_x_1621_);
v_r_1625_ = lean_box(v_res_1624_);
return v_r_1625_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v_suppressElabErrors_1626_, uint8_t v___x_1627_, lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 1)
{
lean_object* v_pre_1629_; 
v_pre_1629_ = lean_ctor_get(v_x_1628_, 0);
switch(lean_obj_tag(v_pre_1629_))
{
case 1:
{
lean_object* v_pre_1630_; 
v_pre_1630_ = lean_ctor_get(v_pre_1629_, 0);
switch(lean_obj_tag(v_pre_1630_))
{
case 0:
{
lean_object* v_str_1631_; lean_object* v_str_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_str_1631_ = lean_ctor_get(v_x_1628_, 1);
v_str_1632_ = lean_ctor_get(v_pre_1629_, 1);
v___x_1633_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1634_ = lean_string_dec_eq(v_str_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1636_ = lean_string_dec_eq(v_str_1632_, v___x_1635_);
if (v___x_1636_ == 0)
{
return v___x_1636_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1638_ = lean_string_dec_eq(v_str_1631_, v___x_1637_);
if (v___x_1638_ == 0)
{
return v___x_1638_;
}
else
{
return v_suppressElabErrors_1626_;
}
}
}
else
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1640_ = lean_string_dec_eq(v_str_1631_, v___x_1639_);
if (v___x_1640_ == 0)
{
return v___x_1640_;
}
else
{
return v_suppressElabErrors_1626_;
}
}
}
case 1:
{
lean_object* v_pre_1641_; 
v_pre_1641_ = lean_ctor_get(v_pre_1630_, 0);
if (lean_obj_tag(v_pre_1641_) == 0)
{
lean_object* v_str_1642_; lean_object* v_str_1643_; lean_object* v_str_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v_str_1642_ = lean_ctor_get(v_x_1628_, 1);
v_str_1643_ = lean_ctor_get(v_pre_1629_, 1);
v_str_1644_ = lean_ctor_get(v_pre_1630_, 1);
v___x_1645_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1646_ = lean_string_dec_eq(v_str_1644_, v___x_1645_);
if (v___x_1646_ == 0)
{
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1648_ = lean_string_dec_eq(v_str_1643_, v___x_1647_);
if (v___x_1648_ == 0)
{
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1650_ = lean_string_dec_eq(v_str_1642_, v___x_1649_);
if (v___x_1650_ == 0)
{
return v___x_1650_;
}
else
{
return v_suppressElabErrors_1626_;
}
}
}
}
else
{
return v___x_1627_;
}
}
default: 
{
return v___x_1627_;
}
}
}
case 0:
{
lean_object* v_str_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_str_1651_ = lean_ctor_get(v_x_1628_, 1);
v___x_1652_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1653_ = lean_string_dec_eq(v_str_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
return v___x_1653_;
}
else
{
return v_suppressElabErrors_1626_;
}
}
default: 
{
return v___x_1627_;
}
}
}
else
{
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1654_, lean_object* v___x_1655_, lean_object* v_x_1656_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1657_; uint8_t v___x_11461__boxed_1658_; uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_suppressElabErrors_boxed_1657_ = lean_unbox(v_suppressElabErrors_1654_);
v___x_11461__boxed_1658_ = lean_unbox(v___x_1655_);
v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1657_, v___x_11461__boxed_1658_, v_x_1656_);
lean_dec(v_x_1656_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v_as_1663_, size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_a_1671_; uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_lt(v_i_1665_, v_sz_1664_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref(v___x_1661_);
v___x_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_b_1666_);
return v___x_1676_;
}
else
{
lean_object* v_a_1677_; lean_object* v_snd_1678_; lean_object* v_fst_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1736_; 
v_a_1677_ = lean_array_uget(v_as_1663_, v_i_1665_);
v_snd_1678_ = lean_ctor_get(v_a_1677_, 1);
v_fst_1679_ = lean_ctor_get(v_a_1677_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_a_1677_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1681_ = v_a_1677_;
v_isShared_1682_ = v_isSharedCheck_1736_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snd_1678_);
lean_inc(v_fst_1679_);
lean_dec(v_a_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1736_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v_snd_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1734_; 
v_snd_1683_ = lean_ctor_get(v_snd_1678_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_snd_1678_);
if (v_isSharedCheck_1734_ == 0)
{
lean_object* v_unused_1735_; 
v_unused_1735_ = lean_ctor_get(v_snd_1678_, 0);
lean_dec(v_unused_1735_);
v___x_1685_ = v_snd_1678_;
v_isShared_1686_ = v_isSharedCheck_1734_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_snd_1683_);
lean_dec(v_snd_1678_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1734_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_fileName_1687_; uint8_t v_suppressElabErrors_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___y_1700_; lean_object* v___y_1701_; 
v_fileName_1687_ = lean_ctor_get(v___y_1667_, 0);
v_suppressElabErrors_1688_ = lean_ctor_get_uint8(v___y_1667_, sizeof(void*)*14 + 1);
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_nat_dec_eq(v___x_1662_, v___x_1690_);
lean_inc_ref(v___x_1661_);
v___x_1692_ = l_Lean_FileMap_toPosition(v___x_1661_, v_fst_1679_);
lean_dec(v_fst_1679_);
v___x_1693_ = lean_box(0);
v___x_1694_ = 2;
v___x_1695_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1696_ = l_Lean_Parser_Error_toString(v_snd_1683_);
v___x_1697_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___x_1698_ = l_Lean_MessageData_ofFormat(v___x_1697_);
if (v_suppressElabErrors_1688_ == 0)
{
v___y_1700_ = v___y_1667_;
v___y_1701_ = v___y_1668_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___f_1732_; uint8_t v___x_1733_; 
v___x_1730_ = lean_box(v_suppressElabErrors_1688_);
v___x_1731_ = lean_box(v___x_1691_);
v___f_1732_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1732_, 0, v___x_1730_);
lean_closure_set(v___f_1732_, 1, v___x_1731_);
lean_inc_ref(v___x_1698_);
v___x_1733_ = l_Lean_MessageData_hasTag(v___f_1732_, v___x_1698_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v___x_1698_);
lean_dec_ref(v___x_1692_);
lean_del_object(v___x_1685_);
lean_del_object(v___x_1681_);
v_a_1671_ = v___x_1689_;
goto v___jp_1670_;
}
else
{
v___y_1700_ = v___y_1667_;
v___y_1701_ = v___y_1668_;
goto v___jp_1699_;
}
}
v___jp_1699_:
{
lean_object* v___x_1702_; lean_object* v_currNamespace_1703_; lean_object* v_openDecls_1704_; lean_object* v___x_1706_; 
v___x_1702_ = lean_st_ref_take(v___y_1701_);
v_currNamespace_1703_ = lean_ctor_get(v___y_1700_, 6);
v_openDecls_1704_ = lean_ctor_get(v___y_1700_, 7);
lean_inc(v_openDecls_1704_);
lean_inc(v_currNamespace_1703_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v_openDecls_1704_);
lean_ctor_set(v___x_1685_, 0, v_currNamespace_1703_);
v___x_1706_ = v___x_1685_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_currNamespace_1703_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_openDecls_1704_);
v___x_1706_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 4);
lean_ctor_set(v___x_1681_, 1, v___x_1698_);
lean_ctor_set(v___x_1681_, 0, v___x_1706_);
v___x_1708_ = v___x_1681_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1698_);
v___x_1708_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v_env_1710_; lean_object* v_nextMacroScope_1711_; lean_object* v_ngen_1712_; lean_object* v_auxDeclNGen_1713_; lean_object* v_traceState_1714_; lean_object* v_cache_1715_; lean_object* v_messages_1716_; lean_object* v_infoState_1717_; lean_object* v_snapshotTasks_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
lean_inc_ref(v_fileName_1687_);
v___x_1709_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1709_, 0, v_fileName_1687_);
lean_ctor_set(v___x_1709_, 1, v___x_1692_);
lean_ctor_set(v___x_1709_, 2, v___x_1693_);
lean_ctor_set(v___x_1709_, 3, v___x_1695_);
lean_ctor_set(v___x_1709_, 4, v___x_1708_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*5, v___x_1691_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*5 + 1, v___x_1694_);
lean_ctor_set_uint8(v___x_1709_, sizeof(void*)*5 + 2, v___x_1691_);
v_env_1710_ = lean_ctor_get(v___x_1702_, 0);
v_nextMacroScope_1711_ = lean_ctor_get(v___x_1702_, 1);
v_ngen_1712_ = lean_ctor_get(v___x_1702_, 2);
v_auxDeclNGen_1713_ = lean_ctor_get(v___x_1702_, 3);
v_traceState_1714_ = lean_ctor_get(v___x_1702_, 4);
v_cache_1715_ = lean_ctor_get(v___x_1702_, 5);
v_messages_1716_ = lean_ctor_get(v___x_1702_, 6);
v_infoState_1717_ = lean_ctor_get(v___x_1702_, 7);
v_snapshotTasks_1718_ = lean_ctor_get(v___x_1702_, 8);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1720_ = v___x_1702_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snapshotTasks_1718_);
lean_inc(v_infoState_1717_);
lean_inc(v_messages_1716_);
lean_inc(v_cache_1715_);
lean_inc(v_traceState_1714_);
lean_inc(v_auxDeclNGen_1713_);
lean_inc(v_ngen_1712_);
lean_inc(v_nextMacroScope_1711_);
lean_inc(v_env_1710_);
lean_dec(v___x_1702_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_MessageLog_add(v___x_1709_, v_messages_1716_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 6, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_env_1710_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_nextMacroScope_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_ngen_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_auxDeclNGen_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_traceState_1714_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v_cache_1715_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_infoState_1717_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_snapshotTasks_1718_);
v___x_1724_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_st_ref_put(v___y_1701_, v___x_1724_);
v_a_1671_ = v___x_1689_;
goto v___jp_1670_;
}
}
}
}
}
}
}
}
v___jp_1670_:
{
size_t v___x_1672_; size_t v___x_1673_; 
v___x_1672_ = ((size_t)1ULL);
v___x_1673_ = lean_usize_add(v_i_1665_, v___x_1672_);
v_i_1665_ = v___x_1673_;
v_b_1666_ = v_a_1671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1737_, lean_object* v___x_1738_, lean_object* v_as_1739_, lean_object* v_sz_1740_, lean_object* v_i_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1740_);
lean_dec(v_sz_1740_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1737_, v___x_1738_, v_as_1739_, v_sz_boxed_1746_, v_i_boxed_1747_, v_b_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v_as_1739_);
lean_dec(v___x_1738_);
return v_res_1748_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_box(1);
v___x_1750_ = l_Lean_MessageData_ofFormat(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1755_ = l_Lean_MessageData_ofFormat(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1756_, lean_object* v_x_1757_){
_start:
{
if (lean_obj_tag(v_x_1757_) == 0)
{
return v_x_1756_;
}
else
{
lean_object* v_head_1758_; lean_object* v_tail_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1781_; 
v_head_1758_ = lean_ctor_get(v_x_1757_, 0);
v_tail_1759_ = lean_ctor_get(v_x_1757_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_x_1757_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1761_ = v_x_1757_;
v_isShared_1762_ = v_isSharedCheck_1781_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_tail_1759_);
lean_inc(v_head_1758_);
lean_dec(v_x_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1781_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_before_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1779_; 
v_before_1763_ = lean_ctor_get(v_head_1758_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_head_1758_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_head_1758_, 1);
lean_dec(v_unused_1780_);
v___x_1765_ = v_head_1758_;
v_isShared_1766_ = v_isSharedCheck_1779_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_before_1763_);
lean_dec(v_head_1758_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1779_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 7);
lean_ctor_set(v___x_1765_, 1, v___x_1767_);
lean_ctor_set(v___x_1765_, 0, v_x_1756_);
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_x_1756_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 7);
lean_ctor_set(v___x_1761_, 1, v___x_1770_);
lean_ctor_set(v___x_1761_, 0, v___x_1769_);
v___x_1772_ = v___x_1761_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = l_Lean_MessageData_ofSyntax(v_before_1763_);
v___x_1774_ = l_Lean_indentD(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v_x_1756_ = v___x_1775_;
v_x_1757_ = v_tail_1759_;
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
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1786_ = l_Lean_MessageData_ofFormat(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1787_, lean_object* v_macroStack_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_options_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_options_1791_ = lean_ctor_get(v___y_1789_, 2);
v___x_1792_ = l_Lean_Elab_pp_macroStack;
v___x_1793_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec(v_macroStack_1788_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_msgData_1787_);
return v___x_1794_;
}
else
{
if (lean_obj_tag(v_macroStack_1788_) == 0)
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_msgData_1787_);
return v___x_1795_;
}
else
{
lean_object* v_head_1796_; lean_object* v_after_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1812_; 
v_head_1796_ = lean_ctor_get(v_macroStack_1788_, 0);
lean_inc(v_head_1796_);
v_after_1797_ = lean_ctor_get(v_head_1796_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_head_1796_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v_head_1796_, 0);
lean_dec(v_unused_1813_);
v___x_1799_ = v_head_1796_;
v_isShared_1800_ = v_isSharedCheck_1812_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_after_1797_);
lean_dec(v_head_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1812_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 7);
lean_ctor_set(v___x_1799_, 1, v___x_1801_);
lean_ctor_set(v___x_1799_, 0, v_msgData_1787_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_msgData_1787_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_msgData_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1804_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_MessageData_ofSyntax(v_after_1797_);
v___x_1807_ = l_Lean_indentD(v___x_1806_);
v_msgData_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1808_, 0, v___x_1805_);
lean_ctor_set(v_msgData_1808_, 1, v___x_1807_);
v___x_1809_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1808_, v_macroStack_1788_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1809_);
return v___x_1810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1814_, lean_object* v_macroStack_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1814_, v_macroStack_1815_, v___y_1816_);
lean_dec_ref(v___y_1816_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_ref_1827_; lean_object* v___x_1828_; lean_object* v_a_1829_; lean_object* v_macroStack_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1841_; 
v_ref_1827_ = lean_ctor_get(v___y_1824_, 5);
v___x_1828_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1819_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
v_macroStack_1830_ = lean_ctor_get(v___y_1820_, 1);
v___x_1831_ = l_Lean_Elab_getBetterRef(v_ref_1827_, v_macroStack_1830_);
lean_inc(v_macroStack_1830_);
v___x_1832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1829_, v_macroStack_1830_, v___y_1824_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1831_);
lean_ctor_set(v___x_1837_, 1, v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_fileName_1860_; lean_object* v_fileMap_1861_; lean_object* v_options_1862_; lean_object* v_currRecDepth_1863_; lean_object* v_maxRecDepth_1864_; lean_object* v_ref_1865_; lean_object* v_currNamespace_1866_; lean_object* v_openDecls_1867_; lean_object* v_initHeartbeats_1868_; lean_object* v_maxHeartbeats_1869_; lean_object* v_quotContext_1870_; lean_object* v_currMacroScope_1871_; uint8_t v_diag_1872_; lean_object* v_cancelTk_x3f_1873_; uint8_t v_suppressElabErrors_1874_; lean_object* v_inheritedTraceOptions_1875_; lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_fileName_1860_ = lean_ctor_get(v___y_1857_, 0);
v_fileMap_1861_ = lean_ctor_get(v___y_1857_, 1);
v_options_1862_ = lean_ctor_get(v___y_1857_, 2);
v_currRecDepth_1863_ = lean_ctor_get(v___y_1857_, 3);
v_maxRecDepth_1864_ = lean_ctor_get(v___y_1857_, 4);
v_ref_1865_ = lean_ctor_get(v___y_1857_, 5);
v_currNamespace_1866_ = lean_ctor_get(v___y_1857_, 6);
v_openDecls_1867_ = lean_ctor_get(v___y_1857_, 7);
v_initHeartbeats_1868_ = lean_ctor_get(v___y_1857_, 8);
v_maxHeartbeats_1869_ = lean_ctor_get(v___y_1857_, 9);
v_quotContext_1870_ = lean_ctor_get(v___y_1857_, 10);
v_currMacroScope_1871_ = lean_ctor_get(v___y_1857_, 11);
v_diag_1872_ = lean_ctor_get_uint8(v___y_1857_, sizeof(void*)*14);
v_cancelTk_x3f_1873_ = lean_ctor_get(v___y_1857_, 12);
v_suppressElabErrors_1874_ = lean_ctor_get_uint8(v___y_1857_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1875_ = lean_ctor_get(v___y_1857_, 13);
v_ref_1876_ = l_Lean_replaceRef(v_ref_1851_, v_ref_1865_);
lean_inc_ref(v_inheritedTraceOptions_1875_);
lean_inc(v_cancelTk_x3f_1873_);
lean_inc(v_currMacroScope_1871_);
lean_inc(v_quotContext_1870_);
lean_inc(v_maxHeartbeats_1869_);
lean_inc(v_initHeartbeats_1868_);
lean_inc(v_openDecls_1867_);
lean_inc(v_currNamespace_1866_);
lean_inc(v_maxRecDepth_1864_);
lean_inc(v_currRecDepth_1863_);
lean_inc_ref(v_options_1862_);
lean_inc_ref(v_fileMap_1861_);
lean_inc_ref(v_fileName_1860_);
v___x_1877_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1877_, 0, v_fileName_1860_);
lean_ctor_set(v___x_1877_, 1, v_fileMap_1861_);
lean_ctor_set(v___x_1877_, 2, v_options_1862_);
lean_ctor_set(v___x_1877_, 3, v_currRecDepth_1863_);
lean_ctor_set(v___x_1877_, 4, v_maxRecDepth_1864_);
lean_ctor_set(v___x_1877_, 5, v_ref_1876_);
lean_ctor_set(v___x_1877_, 6, v_currNamespace_1866_);
lean_ctor_set(v___x_1877_, 7, v_openDecls_1867_);
lean_ctor_set(v___x_1877_, 8, v_initHeartbeats_1868_);
lean_ctor_set(v___x_1877_, 9, v_maxHeartbeats_1869_);
lean_ctor_set(v___x_1877_, 10, v_quotContext_1870_);
lean_ctor_set(v___x_1877_, 11, v_currMacroScope_1871_);
lean_ctor_set(v___x_1877_, 12, v_cancelTk_x3f_1873_);
lean_ctor_set(v___x_1877_, 13, v_inheritedTraceOptions_1875_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*14, v_diag_1872_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*14 + 1, v_suppressElabErrors_1874_);
v___x_1878_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___x_1877_, v___y_1858_);
lean_dec_ref_known(v___x_1877_, 14);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1879_, lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1879_, v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_ref_1879_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; uint8_t v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; 
lean_inc(v_docComment_1889_);
v___x_2047_ = l_Lean_Syntax_getKind(v_docComment_1889_);
v___x_2048_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2049_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2050_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2051_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2052_ = lean_name_eq(v___x_2047_, v___x_2051_);
lean_dec(v___x_2047_);
if (v___x_2052_ == 0)
{
goto v___jp_2024_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = l_Lean_Syntax_getArg(v_docComment_1889_, v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 1)
{
lean_object* v_kind_2055_; 
v_kind_2055_ = lean_ctor_get(v___x_2054_, 1);
lean_inc(v_kind_2055_);
if (lean_obj_tag(v_kind_2055_) == 1)
{
lean_object* v_pre_2056_; 
v_pre_2056_ = lean_ctor_get(v_kind_2055_, 0);
lean_inc(v_pre_2056_);
if (lean_obj_tag(v_pre_2056_) == 1)
{
lean_object* v_pre_2057_; 
v_pre_2057_ = lean_ctor_get(v_pre_2056_, 0);
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
if (lean_obj_tag(v_pre_2059_) == 0)
{
lean_object* v_info_2060_; lean_object* v_args_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2085_; 
v_info_2060_ = lean_ctor_get(v___x_2054_, 0);
v_args_2061_ = lean_ctor_get(v___x_2054_, 2);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2054_, 1);
lean_dec(v_unused_2086_);
v___x_2063_ = v___x_2054_;
v_isShared_2064_ = v_isSharedCheck_2085_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_args_2061_);
lean_inc(v_info_2060_);
lean_dec(v___x_2054_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2085_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_str_2065_; lean_object* v_str_2066_; lean_object* v_str_2067_; lean_object* v_str_2068_; uint8_t v___x_2069_; 
v_str_2065_ = lean_ctor_get(v_kind_2055_, 1);
lean_inc_ref(v_str_2065_);
lean_dec_ref_known(v_kind_2055_, 2);
v_str_2066_ = lean_ctor_get(v_pre_2056_, 1);
lean_inc_ref(v_str_2066_);
lean_dec_ref_known(v_pre_2056_, 2);
v_str_2067_ = lean_ctor_get(v_pre_2057_, 1);
lean_inc_ref(v_str_2067_);
lean_dec_ref_known(v_pre_2057_, 2);
v_str_2068_ = lean_ctor_get(v_pre_2058_, 1);
lean_inc_ref(v_str_2068_);
lean_dec_ref_known(v_pre_2058_, 2);
v___x_2069_ = lean_string_dec_eq(v_str_2068_, v___x_2048_);
lean_dec_ref(v_str_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_str_2067_);
lean_dec_ref(v_str_2066_);
lean_dec_ref(v_str_2065_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_args_2061_);
lean_dec(v_info_2060_);
goto v___jp_2024_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_string_dec_eq(v_str_2067_, v___x_2049_);
lean_dec_ref(v_str_2067_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_str_2066_);
lean_dec_ref(v_str_2065_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_args_2061_);
lean_dec(v_info_2060_);
goto v___jp_2024_;
}
else
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_string_dec_eq(v_str_2066_, v___x_2050_);
lean_dec_ref(v_str_2066_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_str_2065_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_args_2061_);
lean_dec(v_info_2060_);
goto v___jp_2024_;
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2073_ = lean_string_dec_eq(v_str_2065_, v___x_2072_);
lean_dec_ref(v_str_2065_);
if (v___x_2073_ == 0)
{
lean_del_object(v___x_2063_);
lean_dec_ref(v_args_2061_);
lean_dec(v_info_2060_);
goto v___jp_2024_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
lean_dec(v_docComment_1889_);
v___x_2074_ = l_Lean_Name_str___override(v_pre_2059_, v___x_2048_);
v___x_2075_ = l_Lean_Name_str___override(v___x_2074_, v___x_2049_);
v___x_2076_ = l_Lean_Name_str___override(v___x_2075_, v___x_2050_);
v___x_2077_ = l_Lean_Name_str___override(v___x_2076_, v___x_2072_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2077_);
v___x_2079_ = v___x_2063_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_info_2060_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_args_2061_);
v___x_2079_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = l_Lean_Syntax_getArg(v___x_2079_, v___x_2080_);
lean_dec_ref(v___x_2079_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2058_, 2);
lean_dec(v_pre_2059_);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_kind_2055_, 2);
lean_dec_ref_known(v___x_2054_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_pre_2058_);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_kind_2055_, 2);
lean_dec_ref_known(v___x_2054_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_pre_2057_);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_kind_2055_, 2);
lean_dec_ref_known(v___x_2054_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_pre_2056_);
lean_dec_ref_known(v_kind_2055_, 2);
lean_dec_ref_known(v___x_2054_, 3);
goto v___jp_2024_;
}
}
else
{
lean_dec_ref_known(v___x_2054_, 3);
lean_dec(v_kind_2055_);
goto v___jp_2024_;
}
}
else
{
lean_dec(v___x_2054_);
goto v___jp_2024_;
}
}
v___jp_1897_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
return v___x_1899_;
}
v___jp_1900_:
{
lean_object* v___x_1910_; lean_object* v_currNamespace_1911_; lean_object* v_openDecls_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_env_1916_; lean_object* v_nextMacroScope_1917_; lean_object* v_ngen_1918_; lean_object* v_auxDeclNGen_1919_; lean_object* v_traceState_1920_; lean_object* v_cache_1921_; lean_object* v_messages_1922_; lean_object* v_infoState_1923_; lean_object* v_snapshotTasks_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1933_; 
v___x_1910_ = lean_st_ref_take(v___y_1909_);
v_currNamespace_1911_ = lean_ctor_get(v___y_1908_, 6);
v_openDecls_1912_ = lean_ctor_get(v___y_1908_, 7);
lean_inc(v_openDecls_1912_);
lean_inc(v_currNamespace_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_currNamespace_1911_);
lean_ctor_set(v___x_1913_, 1, v_openDecls_1912_);
v___x_1914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___y_1903_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1905_);
v___x_1915_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1915_, 0, v___y_1905_);
lean_ctor_set(v___x_1915_, 1, v___y_1902_);
lean_ctor_set(v___x_1915_, 2, v___y_1901_);
lean_ctor_set(v___x_1915_, 3, v___y_1906_);
lean_ctor_set(v___x_1915_, 4, v___x_1914_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5, v___y_1904_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5 + 1, v___y_1907_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*5 + 2, v___y_1904_);
v_env_1916_ = lean_ctor_get(v___x_1910_, 0);
v_nextMacroScope_1917_ = lean_ctor_get(v___x_1910_, 1);
v_ngen_1918_ = lean_ctor_get(v___x_1910_, 2);
v_auxDeclNGen_1919_ = lean_ctor_get(v___x_1910_, 3);
v_traceState_1920_ = lean_ctor_get(v___x_1910_, 4);
v_cache_1921_ = lean_ctor_get(v___x_1910_, 5);
v_messages_1922_ = lean_ctor_get(v___x_1910_, 6);
v_infoState_1923_ = lean_ctor_get(v___x_1910_, 7);
v_snapshotTasks_1924_ = lean_ctor_get(v___x_1910_, 8);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1926_ = v___x_1910_;
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
lean_dec(v___x_1910_);
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
v___x_1931_ = lean_st_ref_put(v___y_1909_, v___x_1930_);
goto v___jp_1897_;
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
lean_dec_ref(v___y_1940_);
v___x_1946_ = lean_box(0);
v_sz_1947_ = lean_array_size(v___x_1942_);
v___x_1948_ = ((size_t)0ULL);
lean_inc_ref(v___y_1936_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1936_, v___x_1943_, v___x_1942_, v_sz_1947_, v___x_1948_, v___x_1946_, v___y_1894_, v___y_1895_);
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
v___x_1969_ = l_Lean_Parser_InputContext_atEnd(v___y_1940_, v_pos_1968_);
lean_dec_ref(v___y_1940_);
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
v___x_1975_ = lean_string_utf8_get(v___y_1937_, v_pos_1968_);
lean_dec(v_pos_1968_);
v___x_1976_ = lean_string_push(v___x_1973_, v___x_1975_);
v___x_1977_ = lean_string_append(v___x_1974_, v___x_1976_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1979_ = lean_string_append(v___x_1977_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
if (v___y_1938_ == 0)
{
v___y_1901_ = v___x_1971_;
v___y_1902_ = v___x_1970_;
v___y_1903_ = v___x_1981_;
v___y_1904_ = v___x_1969_;
v___y_1905_ = v___y_1939_;
v___y_1906_ = v___x_1973_;
v___y_1907_ = v___x_1972_;
v___y_1908_ = v___y_1894_;
v___y_1909_ = v___y_1895_;
goto v___jp_1900_;
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
goto v___jp_1897_;
}
else
{
v___y_1901_ = v___x_1971_;
v___y_1902_ = v___x_1970_;
v___y_1903_ = v___x_1981_;
v___y_1904_ = v___x_1969_;
v___y_1905_ = v___y_1939_;
v___y_1906_ = v___x_1973_;
v___y_1907_ = v___x_1972_;
v___y_1908_ = v___y_1894_;
v___y_1909_ = v___y_1895_;
goto v___jp_1900_;
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
v___x_2001_ = lean_st_ref_get(v___y_1895_);
v_env_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc_ref_n(v_env_2002_, 2);
lean_dec(v___x_2001_);
lean_inc(v___y_2000_);
lean_inc_ref_n(v___y_1995_, 2);
lean_inc_ref(v___y_1999_);
lean_inc_ref(v___y_1990_);
v_ictx_2003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2003_, 0, v___y_1990_);
lean_ctor_set(v_ictx_2003_, 1, v___y_1999_);
lean_ctor_set(v_ictx_2003_, 2, v___y_1995_);
lean_ctor_set(v_ictx_2003_, 3, v___y_2000_);
lean_inc(v___y_1994_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1993_);
v_pmctx_2004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2004_, 0, v_env_2002_);
lean_ctor_set(v_pmctx_2004_, 1, v___y_1993_);
lean_ctor_set(v_pmctx_2004_, 2, v___y_1997_);
lean_ctor_set(v_pmctx_2004_, 3, v___y_1994_);
lean_inc(v___y_1992_);
v_blockCtxt_2005_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1995_, v___y_1992_, v___y_2000_);
v___x_2006_ = l_Lean_Parser_mkParserState(v___y_1990_);
lean_inc_ref(v___x_2006_);
v_s_2007_ = l_Lean_Parser_ParserState_setPos(v___x_2006_, v___y_1992_);
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
lean_dec(v___y_1996_);
v___y_1935_ = v___y_1991_;
v___y_1936_ = v___y_1995_;
v___y_1937_ = v___y_1990_;
v___y_1938_ = v___y_1998_;
v___y_1939_ = v___y_1999_;
v___y_1940_ = v_ictx_2003_;
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
lean_ctor_set(v___x_2019_, 0, v___y_1996_);
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
v___y_1935_ = v___y_1991_;
v___y_1936_ = v___y_1995_;
v___y_1937_ = v___y_1990_;
v___y_1938_ = v___y_1998_;
v___y_1939_ = v___y_1999_;
v___y_1940_ = v_ictx_2003_;
v___y_1941_ = v___x_2023_;
goto v___jp_1934_;
}
else
{
lean_dec(v_pos_2015_);
lean_dec_ref(v___x_2009_);
lean_dec_ref(v___x_2006_);
lean_dec_ref_known(v_pmctx_2004_, 4);
lean_dec(v___y_1996_);
v___y_1935_ = v___y_1991_;
v___y_1936_ = v___y_1995_;
v___y_1937_ = v___y_1990_;
v___y_1938_ = v___y_1998_;
v___y_1939_ = v___y_1999_;
v___y_1940_ = v_ictx_2003_;
v___y_1941_ = v_s_2010_;
goto v___jp_1934_;
}
}
}
v___jp_2024_:
{
lean_object* v_fileName_2025_; lean_object* v_fileMap_2026_; lean_object* v_options_2027_; lean_object* v_currNamespace_2028_; lean_object* v_openDecls_2029_; uint8_t v_suppressElabErrors_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; 
v_fileName_2025_ = lean_ctor_get(v___y_1894_, 0);
v_fileMap_2026_ = lean_ctor_get(v___y_1894_, 1);
v_options_2027_ = lean_ctor_get(v___y_1894_, 2);
v_currNamespace_2028_ = lean_ctor_get(v___y_1894_, 6);
v_openDecls_2029_ = lean_ctor_get(v___y_1894_, 7);
v_suppressElabErrors_2030_ = lean_ctor_get_uint8(v___y_1894_, sizeof(void*)*14 + 1);
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = l_Lean_Syntax_getArg(v_docComment_1889_, v___x_2031_);
v___x_2033_ = 1;
v___x_2034_ = l_Lean_Syntax_getPos_x3f(v___x_2032_, v___x_2033_);
if (lean_obj_tag(v___x_2034_) == 1)
{
lean_object* v_val_2035_; lean_object* v___x_2036_; 
v_val_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_val_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_Syntax_getTailPos_x3f(v___x_2032_, v___x_2033_);
lean_dec(v___x_2032_);
if (lean_obj_tag(v___x_2036_) == 1)
{
lean_object* v_val_2037_; lean_object* v_source_2038_; lean_object* v___x_2039_; lean_object* v_endPos_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
lean_dec(v_docComment_1889_);
v_val_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v_source_2038_ = lean_ctor_get(v_fileMap_2026_, 0);
v___x_2039_ = lean_string_utf8_prev(v_source_2038_, v_val_2037_);
lean_dec(v_val_2037_);
v_endPos_2040_ = lean_string_utf8_prev(v_source_2038_, v___x_2039_);
lean_dec(v___x_2039_);
v___x_2041_ = lean_string_utf8_byte_size(v_source_2038_);
v___x_2042_ = lean_nat_dec_le(v_endPos_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_dec(v_endPos_2040_);
v___y_1990_ = v_source_2038_;
v___y_1991_ = v_suppressElabErrors_2030_;
v___y_1992_ = v_val_2035_;
v___y_1993_ = v_options_2027_;
v___y_1994_ = v_openDecls_2029_;
v___y_1995_ = v_fileMap_2026_;
v___y_1996_ = v___x_2031_;
v___y_1997_ = v_currNamespace_2028_;
v___y_1998_ = v_suppressElabErrors_2030_;
v___y_1999_ = v_fileName_2025_;
v___y_2000_ = v___x_2041_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v_source_2038_;
v___y_1991_ = v_suppressElabErrors_2030_;
v___y_1992_ = v_val_2035_;
v___y_1993_ = v_options_2027_;
v___y_1994_ = v_openDecls_2029_;
v___y_1995_ = v_fileMap_2026_;
v___y_1996_ = v___x_2031_;
v___y_1997_ = v_currNamespace_2028_;
v___y_1998_ = v_suppressElabErrors_2030_;
v___y_1999_ = v_fileName_2025_;
v___y_2000_ = v_endPos_2040_;
goto v___jp_1989_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v___x_2036_);
lean_dec(v_val_2035_);
v___x_2043_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2044_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1889_, v___x_2043_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v_docComment_1889_);
return v___x_2044_;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec(v___x_2034_);
lean_dec(v___x_2032_);
v___x_2045_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2046_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1889_, v___x_2045_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v_docComment_1889_);
return v___x_2046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2109_, lean_object* v_binders_2110_, lean_object* v_docComment_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v_body_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = lean_unsigned_to_nat(1u);
v_body_2120_ = l_Lean_Syntax_getArg(v_docComment_2111_, v___x_2119_);
v___x_2121_ = 1;
v___x_2122_ = l_Lean_Syntax_getPos_x3f(v_body_2120_, v___x_2121_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2120_);
v___x_2124_ = l_Lean_Syntax_isOfKind(v_body_2120_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec(v_body_2120_);
v___x_2125_ = l_Lean_TSyntax_getDocString(v_docComment_2111_);
lean_dec(v_docComment_2111_);
v___x_2126_ = l_Lean_versoDocStringOfText(v_declName_2109_, v_binders_2110_, v___x_2125_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
lean_dec(v_docComment_2111_);
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l_Lean_Syntax_getArg(v_body_2120_, v___x_2127_);
lean_dec(v_body_2120_);
v___x_2129_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2128_);
v___x_2130_ = l_Lean_Syntax_isOfKind(v___x_2128_, v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_Syntax_getArgs(v___x_2128_);
lean_dec(v___x_2128_);
v___x_2132_ = lean_box(0);
v___x_2133_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2109_, v_binders_2110_, v___x_2131_, v___x_2132_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = l_Lean_Syntax_getArg(v___x_2128_, v___x_2127_);
lean_dec(v___x_2128_);
v___x_2135_ = l_Lean_Syntax_getAtomVal(v___x_2134_);
lean_dec(v___x_2134_);
v___x_2136_ = l_Lean_versoDocStringOfText(v_declName_2109_, v_binders_2110_, v___x_2135_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2136_;
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref_known(v___x_2122_, 1);
lean_dec(v_body_2120_);
v___x_2137_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2188_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2188_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2188_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
if (lean_obj_tag(v_a_2138_) == 1)
{
lean_object* v_val_2142_; lean_object* v___x_2143_; size_t v_sz_2144_; size_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; 
lean_del_object(v___x_2140_);
v_val_2142_ = lean_ctor_get(v_a_2138_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v_a_2138_, 1);
v___x_2143_ = l_Lean_Syntax_getArgs(v_val_2142_);
lean_dec(v_val_2142_);
v_sz_2144_ = lean_array_size(v___x_2143_);
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2144_, v___x_2145_, v___x_2143_);
v___x_2147_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2147_, 0, v___x_2146_);
v___x_2148_ = 0;
v___x_2149_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2109_, v_binders_2110_, v___x_2147_, v___x_2148_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2175_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2175_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_fst_2154_; lean_object* v_snd_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2174_; 
v_fst_2154_ = lean_ctor_get(v_a_2150_, 0);
v_snd_2155_ = lean_ctor_get(v_a_2150_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_a_2150_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2157_ = v_a_2150_;
v_isShared_2158_ = v_isSharedCheck_2174_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_snd_2155_);
lean_inc(v_fst_2154_);
lean_dec(v_a_2150_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2174_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v_fst_2159_; lean_object* v_snd_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2173_; 
v_fst_2159_ = lean_ctor_get(v_fst_2154_, 0);
v_snd_2160_ = lean_ctor_get(v_fst_2154_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_fst_2154_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2162_ = v_fst_2154_;
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_snd_2160_);
lean_inc(v_fst_2159_);
lean_dec(v_fst_2154_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2173_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_fst_2159_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_snd_2160_);
v___x_2165_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2165_);
v___x_2167_ = v___x_2157_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2155_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2167_);
v___x_2169_ = v___x_2152_;
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
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2149_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2149_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec(v_a_2138_);
lean_dec(v_binders_2110_);
lean_dec(v_declName_2109_);
v___x_2184_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2184_);
v___x_2186_ = v___x_2140_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_binders_2110_);
lean_dec(v_declName_2109_);
v_a_2189_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2137_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2137_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2197_, lean_object* v_binders_2198_, lean_object* v_docComment_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_versoDocString(v_declName_2197_, v_binders_2198_, v_docComment_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2208_, lean_object* v___x_2209_, lean_object* v_as_2210_, size_t v_sz_2211_, size_t v_i_2212_, lean_object* v_b_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2208_, v___x_2209_, v_as_2210_, v_sz_2211_, v_i_2212_, v_b_2213_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_as_2224_, lean_object* v_sz_2225_, lean_object* v_i_2226_, lean_object* v_b_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
size_t v_sz_boxed_2235_; size_t v_i_boxed_2236_; lean_object* v_res_2237_; 
v_sz_boxed_2235_ = lean_unbox_usize(v_sz_2225_);
lean_dec(v_sz_2225_);
v_i_boxed_2236_ = lean_unbox_usize(v_i_2226_);
lean_dec(v_i_2226_);
v_res_2237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2222_, v___x_2223_, v_as_2224_, v_sz_boxed_2235_, v_i_boxed_2236_, v_b_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_as_2224_);
lean_dec(v___x_2223_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2238_, lean_object* v_ref_2239_, lean_object* v_msg_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2239_, v_msg_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_ref_2250_, lean_object* v_msg_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2249_, v_ref_2250_, v_msg_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v_ref_2250_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2260_, lean_object* v_msg_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_msg_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2270_, v_msg_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2280_, lean_object* v_macroStack_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2280_, v_macroStack_2281_, v___y_2286_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2290_, lean_object* v_macroStack_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2290_, v_macroStack_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2300_, lean_object* v_doc_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2317_; lean_object* v_env_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2309_ = lean_st_ref_get(v_a_2307_);
v_env_2324_ = lean_ctor_get(v___x_2309_, 0);
lean_inc_ref(v_env_2324_);
lean_dec(v___x_2309_);
v___x_2325_ = l_Lean_getMainVersoModuleDocs(v_env_2324_);
v___x_2326_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2325_);
lean_dec_ref(v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
v___y_2317_ = v___x_2326_;
goto v___jp_2316_;
}
else
{
lean_object* v_val_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2336_; 
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_val_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_add(v_val_2327_, v___x_2331_);
lean_dec(v_val_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2332_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
v___y_2317_ = v___x_2334_;
goto v___jp_2316_;
}
}
}
v___jp_2310_:
{
lean_object* v___x_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2313_, 0, v_range_2300_);
lean_closure_set(v___x_2313_, 1, v___y_2311_);
lean_closure_set(v___x_2313_, 2, v___y_2312_);
v___x_2314_ = 0;
v___x_2315_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2313_, v___x_2314_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
return v___x_2315_;
}
v___jp_2316_:
{
lean_object* v___x_2318_; size_t v_sz_2319_; size_t v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = l_Lean_Syntax_getArgs(v_doc_2301_);
v_sz_2319_ = lean_array_size(v___x_2318_);
v___x_2320_ = ((size_t)0ULL);
v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2319_, v___x_2320_, v___x_2318_);
if (lean_obj_tag(v___y_2317_) == 0)
{
lean_object* v___x_2322_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
v___y_2311_ = v___x_2321_;
v___y_2312_ = v___x_2322_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2323_; 
v_val_2323_ = lean_ctor_get(v___y_2317_, 0);
lean_inc(v_val_2323_);
lean_dec_ref_known(v___y_2317_, 1);
v___y_2311_ = v___x_2321_;
v___y_2312_ = v_val_2323_;
goto v___jp_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2337_, lean_object* v_doc_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_versoModDocString(v_range_2337_, v_doc_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec_ref(v_a_2339_);
lean_dec(v_doc_2338_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2356_, lean_object* v_docComment_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2366_ = l_Lean_versoDocStringOfText(v_declName_2356_, v___x_2365_, v_docComment_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2367_, lean_object* v_docComment_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_versoDocStringFromString(v_declName_2367_, v_docComment_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2377_, lean_object* v_declName_2378_, lean_object* v_env_2379_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2380_ = l_Lean_docStringExt;
v___x_2381_ = l_String_removeLeadingSpaces(v_docString_2377_);
v___x_2382_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2380_, v_env_2379_, v_declName_2378_, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2383_, lean_object* v_modifyEnv_2384_, lean_object* v_docString_2385_){
_start:
{
lean_object* v___f_2386_; lean_object* v___x_2387_; 
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2386_, 0, v_docString_2385_);
lean_closure_set(v___f_2386_, 1, v_declName_2383_);
v___x_2387_ = lean_apply_1(v_modifyEnv_2384_, v___f_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_docComment_2390_, lean_object* v_toBind_2391_, lean_object* v___f_2392_, lean_object* v_____r_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = l_Lean_getDocStringText___redArg(v_inst_2388_, v_inst_2389_, v_docComment_2390_);
v___x_2395_ = lean_apply_4(v_toBind_2391_, lean_box(0), lean_box(0), v___x_2394_, v___f_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_docComment_2401_, lean_object* v_toBind_2402_, lean_object* v___f_2403_, lean_object* v_____r_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = l_Lean_validateDocComment___redArg(v_inst_2396_, v_inst_2397_, v_inst_2398_, v_inst_2399_, v_inst_2400_, v_docComment_2401_);
v___x_2406_ = lean_apply_4(v_toBind_2402_, lean_box(0), lean_box(0), v___x_2405_, v___f_2403_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_docComment_2412_, lean_object* v_toBind_2413_, lean_object* v___f_2414_, lean_object* v_____r_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2407_, v_inst_2408_, v_inst_2409_, v_inst_2410_, v_inst_2411_, v_docComment_2412_, v_toBind_2413_, v___f_2414_, v_____r_2415_);
lean_dec(v_docComment_2412_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2417_, lean_object* v_____r_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_apply_1(v___f_2417_, v_____r_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2426_, lean_object* v_declName_2427_, uint8_t v___x_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_toBind_2431_, lean_object* v___f_2432_, lean_object* v_____do__lift_2433_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2433_, v_declName_2427_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_dec(v___f_2432_);
lean_dec(v_toBind_2431_);
lean_dec_ref(v_inst_2430_);
lean_dec_ref(v_inst_2429_);
lean_dec(v_declName_2427_);
goto v___jp_2434_;
}
else
{
lean_dec_ref_known(v___x_2437_, 1);
if (v___x_2428_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec(v___f_2426_);
v___x_2438_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2439_ = l_Lean_MessageData_ofConstName(v_declName_2427_, v___x_2428_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_throwError___redArg(v_inst_2429_, v_inst_2430_, v___x_2442_);
v___x_2444_ = lean_apply_4(v_toBind_2431_, lean_box(0), lean_box(0), v___x_2443_, v___f_2432_);
return v___x_2444_;
}
else
{
lean_dec(v___f_2432_);
lean_dec(v_toBind_2431_);
lean_dec_ref(v_inst_2430_);
lean_dec_ref(v_inst_2429_);
lean_dec(v_declName_2427_);
goto v___jp_2434_;
}
}
v___jp_2434_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = lean_apply_1(v___f_2426_, v___x_2435_);
return v___x_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2445_, lean_object* v_declName_2446_, lean_object* v___x_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_toBind_2450_, lean_object* v___f_2451_, lean_object* v_____do__lift_2452_){
_start:
{
uint8_t v___x_243__boxed_2453_; lean_object* v_res_2454_; 
v___x_243__boxed_2453_ = lean_unbox(v___x_2447_);
v_res_2454_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2445_, v_declName_2446_, v___x_243__boxed_2453_, v_inst_2448_, v_inst_2449_, v_toBind_2450_, v___f_2451_, v_____do__lift_2452_);
lean_dec_ref(v_____do__lift_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_declName_2462_, lean_object* v_docComment_2463_){
_start:
{
lean_object* v_toApplicative_2464_; lean_object* v_toBind_2465_; lean_object* v_toPure_2466_; uint8_t v___x_2467_; 
v_toApplicative_2464_ = lean_ctor_get(v_inst_2455_, 0);
v_toBind_2465_ = lean_ctor_get(v_inst_2455_, 1);
lean_inc(v_toBind_2465_);
v_toPure_2466_ = lean_ctor_get(v_toApplicative_2464_, 1);
v___x_2467_ = l_Lean_Name_isAnonymous(v_declName_2462_);
if (v___x_2467_ == 0)
{
lean_object* v_getEnv_2468_; lean_object* v_modifyEnv_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___f_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
v_getEnv_2468_ = lean_ctor_get(v_inst_2458_, 0);
lean_inc(v_getEnv_2468_);
v_modifyEnv_2469_ = lean_ctor_get(v_inst_2458_, 1);
lean_inc(v_modifyEnv_2469_);
lean_dec_ref(v_inst_2458_);
lean_inc(v_declName_2462_);
v___f_2470_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2470_, 0, v_declName_2462_);
lean_closure_set(v___f_2470_, 1, v_modifyEnv_2469_);
lean_inc_n(v_toBind_2465_, 3);
lean_inc(v_docComment_2463_);
lean_inc_ref(v_inst_2459_);
lean_inc_ref_n(v_inst_2455_, 2);
v___f_2471_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2471_, 0, v_inst_2455_);
lean_closure_set(v___f_2471_, 1, v_inst_2459_);
lean_closure_set(v___f_2471_, 2, v_docComment_2463_);
lean_closure_set(v___f_2471_, 3, v_toBind_2465_);
lean_closure_set(v___f_2471_, 4, v___f_2470_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2472_, 0, v_inst_2455_);
lean_closure_set(v___f_2472_, 1, v_inst_2456_);
lean_closure_set(v___f_2472_, 2, v_inst_2460_);
lean_closure_set(v___f_2472_, 3, v_inst_2461_);
lean_closure_set(v___f_2472_, 4, v_inst_2457_);
lean_closure_set(v___f_2472_, 5, v_docComment_2463_);
lean_closure_set(v___f_2472_, 6, v_toBind_2465_);
lean_closure_set(v___f_2472_, 7, v___f_2471_);
lean_inc_ref(v___f_2472_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2473_, 0, v___f_2472_);
v___x_2474_ = lean_box(v___x_2467_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2475_, 0, v___f_2472_);
lean_closure_set(v___f_2475_, 1, v_declName_2462_);
lean_closure_set(v___f_2475_, 2, v___x_2474_);
lean_closure_set(v___f_2475_, 3, v_inst_2455_);
lean_closure_set(v___f_2475_, 4, v_inst_2459_);
lean_closure_set(v___f_2475_, 5, v_toBind_2465_);
lean_closure_set(v___f_2475_, 6, v___f_2473_);
v___x_2476_ = lean_apply_4(v_toBind_2465_, lean_box(0), lean_box(0), v_getEnv_2468_, v___f_2475_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_inc(v_toPure_2466_);
lean_dec(v_toBind_2465_);
lean_dec(v_docComment_2463_);
lean_dec(v_declName_2462_);
lean_dec(v_inst_2461_);
lean_dec_ref(v_inst_2460_);
lean_dec_ref(v_inst_2459_);
lean_dec_ref(v_inst_2458_);
lean_dec(v_inst_2457_);
lean_dec(v_inst_2456_);
lean_dec_ref(v_inst_2455_);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_apply_2(v_toPure_2466_, lean_box(0), v___x_2477_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_declName_2487_, lean_object* v_docComment_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_addMarkdownDocString___redArg(v_inst_2480_, v_inst_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_inst_2486_, v_declName_2487_, v_docComment_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2490_, lean_object* v_x1_2491_, lean_object* v_x2_2492_){
_start:
{
lean_object* v_index_2493_; lean_object* v_sourceString_2494_; lean_object* v_imports_2495_; lean_object* v_currNamespace_2496_; lean_object* v_openDecls_2497_; lean_object* v_options_2498_; lean_object* v_check_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2512_; 
v_index_2493_ = lean_ctor_get(v_x2_2492_, 1);
v_sourceString_2494_ = lean_ctor_get(v_x2_2492_, 2);
v_imports_2495_ = lean_ctor_get(v_x2_2492_, 3);
v_currNamespace_2496_ = lean_ctor_get(v_x2_2492_, 4);
v_openDecls_2497_ = lean_ctor_get(v_x2_2492_, 5);
v_options_2498_ = lean_ctor_get(v_x2_2492_, 6);
v_check_2499_ = lean_ctor_get(v_x2_2492_, 7);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_x2_2492_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v_x2_2492_, 0);
lean_dec(v_unused_2513_);
v___x_2501_ = v_x2_2492_;
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_check_2499_);
lean_inc(v_options_2498_);
lean_inc(v_openDecls_2497_);
lean_inc(v_currNamespace_2496_);
lean_inc(v_imports_2495_);
lean_inc(v_sourceString_2494_);
lean_inc(v_index_2493_);
lean_dec(v_x2_2492_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v_toEnvExtension_2504_; lean_object* v_asyncMode_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2503_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2504_ = lean_ctor_get(v___x_2503_, 0);
v_asyncMode_2505_ = lean_ctor_get(v_toEnvExtension_2504_, 2);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_declName_2490_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2506_);
v___x_2508_ = v___x_2501_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_index_2493_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_sourceString_2494_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_imports_2495_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_currNamespace_2496_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v_openDecls_2497_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_options_2498_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_check_2499_);
v___x_2508_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_box(0);
v___x_2510_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2503_, v_x1_2491_, v___x_2508_, v_asyncMode_2505_, v___x_2509_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2533_, lean_object* v_docs_2534_, lean_object* v_deferred_2535_, lean_object* v___f_2536_, lean_object* v_env_2537_){
_start:
{
lean_object* v___x_2538_; lean_object* v_env_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2538_ = l_Lean_versoDocStringExt;
v_env_2539_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2538_, v_env_2537_, v_declName_2533_, v_docs_2534_);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = lean_array_get_size(v_deferred_2535_);
v___x_2542_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2543_ = lean_nat_dec_lt(v___x_2540_, v___x_2541_);
if (v___x_2543_ == 0)
{
lean_dec_ref(v___f_2536_);
lean_dec_ref(v_deferred_2535_);
return v_env_2539_;
}
else
{
uint8_t v___x_2544_; 
v___x_2544_ = lean_nat_dec_le(v___x_2541_, v___x_2541_);
if (v___x_2544_ == 0)
{
if (v___x_2543_ == 0)
{
lean_dec_ref(v___f_2536_);
lean_dec_ref(v_deferred_2535_);
return v_env_2539_;
}
else
{
size_t v___x_2545_; size_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = ((size_t)0ULL);
v___x_2546_ = lean_usize_of_nat(v___x_2541_);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2542_, v___f_2536_, v_deferred_2535_, v___x_2545_, v___x_2546_, v_env_2539_);
return v___x_2547_;
}
}
else
{
size_t v___x_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = lean_usize_of_nat(v___x_2541_);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2542_, v___f_2536_, v_deferred_2535_, v___x_2548_, v___x_2549_, v_env_2539_);
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2551_, lean_object* v___f_2552_, lean_object* v_____r_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_apply_1(v_modifyEnv_2551_, v___f_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2557_, lean_object* v_modifyEnv_2558_, lean_object* v___f_2559_, uint8_t v___x_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_toBind_2563_, lean_object* v___f_2564_, lean_object* v_____do__lift_2565_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2565_, v_declName_2557_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec(v___f_2564_);
lean_dec(v_toBind_2563_);
lean_dec_ref(v_inst_2562_);
lean_dec_ref(v_inst_2561_);
lean_dec(v_declName_2557_);
v___x_2567_ = lean_apply_1(v_modifyEnv_2558_, v___f_2559_);
return v___x_2567_;
}
else
{
lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2584_; 
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v___x_2566_, 0);
lean_dec(v_unused_2585_);
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2584_;
goto v_resetjp_2568_;
}
else
{
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2584_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
if (v___x_2560_ == 0)
{
lean_object* v___x_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
lean_dec_ref(v___f_2559_);
lean_dec(v_modifyEnv_2558_);
v___x_2571_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2572_ = 1;
v___x_2573_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2557_, v___x_2572_);
v___x_2574_ = lean_string_append(v___x_2571_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
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
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = l_Lean_MessageData_ofFormat(v___x_2578_);
v___x_2580_ = l_Lean_throwError___redArg(v_inst_2561_, v_inst_2562_, v___x_2579_);
v___x_2581_ = lean_apply_4(v_toBind_2563_, lean_box(0), lean_box(0), v___x_2580_, v___f_2564_);
return v___x_2581_;
}
}
else
{
lean_object* v___x_2583_; 
lean_del_object(v___x_2569_);
lean_dec(v___f_2564_);
lean_dec(v_toBind_2563_);
lean_dec_ref(v_inst_2562_);
lean_dec_ref(v_inst_2561_);
lean_dec(v_declName_2557_);
v___x_2583_ = lean_apply_1(v_modifyEnv_2558_, v___f_2559_);
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2586_, lean_object* v_modifyEnv_2587_, lean_object* v___f_2588_, lean_object* v___x_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_toBind_2592_, lean_object* v___f_2593_, lean_object* v_____do__lift_2594_){
_start:
{
uint8_t v___x_371__boxed_2595_; lean_object* v_res_2596_; 
v___x_371__boxed_2595_ = lean_unbox(v___x_2589_);
v_res_2596_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2586_, v_modifyEnv_2587_, v___f_2588_, v___x_371__boxed_2595_, v_inst_2590_, v_inst_2591_, v_toBind_2592_, v___f_2593_, v_____do__lift_2594_);
lean_dec_ref(v_____do__lift_2594_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_declName_2600_, lean_object* v_docs_2601_, lean_object* v_deferred_2602_){
_start:
{
lean_object* v_toApplicative_2603_; lean_object* v_toBind_2604_; lean_object* v_toPure_2605_; uint8_t v___x_2606_; 
v_toApplicative_2603_ = lean_ctor_get(v_inst_2597_, 0);
v_toBind_2604_ = lean_ctor_get(v_inst_2597_, 1);
lean_inc(v_toBind_2604_);
v_toPure_2605_ = lean_ctor_get(v_toApplicative_2603_, 1);
v___x_2606_ = l_Lean_Name_isAnonymous(v_declName_2600_);
if (v___x_2606_ == 0)
{
lean_object* v_getEnv_2607_; lean_object* v_modifyEnv_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___f_2611_; lean_object* v___x_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; 
v_getEnv_2607_ = lean_ctor_get(v_inst_2598_, 0);
lean_inc(v_getEnv_2607_);
v_modifyEnv_2608_ = lean_ctor_get(v_inst_2598_, 1);
lean_inc_n(v_modifyEnv_2608_, 2);
lean_dec_ref(v_inst_2598_);
lean_inc_n(v_declName_2600_, 2);
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2609_, 0, v_declName_2600_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2610_, 0, v_declName_2600_);
lean_closure_set(v___f_2610_, 1, v_docs_2601_);
lean_closure_set(v___f_2610_, 2, v_deferred_2602_);
lean_closure_set(v___f_2610_, 3, v___f_2609_);
lean_inc_ref(v___f_2610_);
v___f_2611_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2611_, 0, v_modifyEnv_2608_);
lean_closure_set(v___f_2611_, 1, v___f_2610_);
v___x_2612_ = lean_box(v___x_2606_);
lean_inc(v_toBind_2604_);
v___f_2613_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2613_, 0, v_declName_2600_);
lean_closure_set(v___f_2613_, 1, v_modifyEnv_2608_);
lean_closure_set(v___f_2613_, 2, v___f_2610_);
lean_closure_set(v___f_2613_, 3, v___x_2612_);
lean_closure_set(v___f_2613_, 4, v_inst_2597_);
lean_closure_set(v___f_2613_, 5, v_inst_2599_);
lean_closure_set(v___f_2613_, 6, v_toBind_2604_);
lean_closure_set(v___f_2613_, 7, v___f_2611_);
v___x_2614_ = lean_apply_4(v_toBind_2604_, lean_box(0), lean_box(0), v_getEnv_2607_, v___f_2613_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_inc(v_toPure_2605_);
lean_dec(v_toBind_2604_);
lean_dec_ref(v_deferred_2602_);
lean_dec_ref(v_docs_2601_);
lean_dec(v_declName_2600_);
lean_dec_ref(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v_inst_2597_);
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_apply_2(v_toPure_2605_, lean_box(0), v___x_2615_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_declName_2622_, lean_object* v_docs_2623_, lean_object* v_deferred_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2618_, v_inst_2619_, v_inst_2621_, v_declName_2622_, v_docs_2623_, v_deferred_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_declName_2631_, lean_object* v_docs_2632_, lean_object* v_deferred_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_addVersoDocStringCore(v_m_2626_, v_inst_2627_, v_inst_2628_, v_inst_2629_, v_inst_2630_, v_declName_2631_, v_docs_2632_, v_deferred_2633_);
lean_dec(v_inst_2629_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2635_, lean_object* v_x1_2636_, lean_object* v_x2_2637_){
_start:
{
lean_object* v_index_2638_; lean_object* v_sourceString_2639_; lean_object* v_imports_2640_; lean_object* v_currNamespace_2641_; lean_object* v_openDecls_2642_; lean_object* v_options_2643_; lean_object* v_check_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2657_; 
v_index_2638_ = lean_ctor_get(v_x2_2637_, 1);
v_sourceString_2639_ = lean_ctor_get(v_x2_2637_, 2);
v_imports_2640_ = lean_ctor_get(v_x2_2637_, 3);
v_currNamespace_2641_ = lean_ctor_get(v_x2_2637_, 4);
v_openDecls_2642_ = lean_ctor_get(v_x2_2637_, 5);
v_options_2643_ = lean_ctor_get(v_x2_2637_, 6);
v_check_2644_ = lean_ctor_get(v_x2_2637_, 7);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_x2_2637_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v_x2_2637_, 0);
lean_dec(v_unused_2658_);
v___x_2646_ = v_x2_2637_;
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_check_2644_);
lean_inc(v_options_2643_);
lean_inc(v_openDecls_2642_);
lean_inc(v_currNamespace_2641_);
lean_inc(v_imports_2640_);
lean_inc(v_sourceString_2639_);
lean_inc(v_index_2638_);
lean_dec(v_x2_2637_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2657_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v_toEnvExtension_2649_; lean_object* v_asyncMode_2650_; lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2648_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2649_ = lean_ctor_get(v___x_2648_, 0);
v_asyncMode_2650_ = lean_ctor_get(v_toEnvExtension_2649_, 2);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_size_2635_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2651_);
v___x_2653_ = v___x_2646_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2651_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_index_2638_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_sourceString_2639_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_imports_2640_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_currNamespace_2641_);
lean_ctor_set(v_reuseFailAlloc_2656_, 5, v_openDecls_2642_);
lean_ctor_set(v_reuseFailAlloc_2656_, 6, v_options_2643_);
lean_ctor_set(v_reuseFailAlloc_2656_, 7, v_check_2644_);
v___x_2653_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_box(0);
v___x_2655_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2648_, v_x1_2636_, v___x_2653_, v_asyncMode_2650_, v___x_2654_);
return v___x_2655_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2661_ = l_Lean_stringToMessageData(v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_deferred_2665_, lean_object* v_inst_2666_, lean_object* v___f_2667_, lean_object* v_____do__lift_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2668_, v_docs_2662_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref(v___f_2667_);
lean_dec_ref(v_inst_2666_);
lean_dec_ref(v_deferred_2665_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2672_ = l_Lean_stringToMessageData(v_a_2670_);
v___x_2673_ = l_Lean_indentD(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = l_Lean_throwError___redArg(v_inst_2663_, v_inst_2664_, v___x_2674_);
return v___x_2675_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
lean_dec_ref(v_inst_2664_);
lean_dec_ref(v_inst_2663_);
v_a_2676_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_array_get_size(v_deferred_2665_);
v___x_2679_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2680_ = lean_nat_dec_lt(v___x_2677_, v___x_2678_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec_ref(v___f_2667_);
lean_dec_ref(v_deferred_2665_);
v___x_2681_ = l_Lean_setEnv___redArg(v_inst_2666_, v_a_2676_);
return v___x_2681_;
}
else
{
uint8_t v___x_2682_; 
v___x_2682_ = lean_nat_dec_le(v___x_2678_, v___x_2678_);
if (v___x_2682_ == 0)
{
if (v___x_2680_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v___f_2667_);
lean_dec_ref(v_deferred_2665_);
v___x_2683_ = l_Lean_setEnv___redArg(v_inst_2666_, v_a_2676_);
return v___x_2683_;
}
else
{
size_t v___x_2684_; size_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2684_ = ((size_t)0ULL);
v___x_2685_ = lean_usize_of_nat(v___x_2678_);
v___x_2686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2679_, v___f_2667_, v_deferred_2665_, v___x_2684_, v___x_2685_, v_a_2676_);
v___x_2687_ = l_Lean_setEnv___redArg(v_inst_2666_, v___x_2686_);
return v___x_2687_;
}
}
else
{
size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2688_ = ((size_t)0ULL);
v___x_2689_ = lean_usize_of_nat(v___x_2678_);
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2679_, v___f_2667_, v_deferred_2665_, v___x_2688_, v___x_2689_, v_a_2676_);
v___x_2691_ = l_Lean_setEnv___redArg(v_inst_2666_, v___x_2690_);
return v___x_2691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_deferred_2695_, lean_object* v_inst_2696_, lean_object* v_toBind_2697_, lean_object* v_getEnv_2698_, lean_object* v_____do__lift_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v_size_2701_; lean_object* v___f_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; 
v___x_2700_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2699_);
v_size_2701_ = lean_ctor_get(v___x_2700_, 2);
lean_inc(v_size_2701_);
lean_dec_ref(v___x_2700_);
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2702_, 0, v_size_2701_);
v___f_2703_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2703_, 0, v_docs_2692_);
lean_closure_set(v___f_2703_, 1, v_inst_2693_);
lean_closure_set(v___f_2703_, 2, v_inst_2694_);
lean_closure_set(v___f_2703_, 3, v_deferred_2695_);
lean_closure_set(v___f_2703_, 4, v_inst_2696_);
lean_closure_set(v___f_2703_, 5, v___f_2702_);
v___x_2704_ = lean_apply_4(v_toBind_2697_, lean_box(0), lean_box(0), v_getEnv_2698_, v___f_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_toBind_2710_, lean_object* v_getEnv_2711_, lean_object* v___f_2712_, lean_object* v_____do__lift_2713_){
_start:
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = l_Lean_getMainModuleDoc(v_____do__lift_2713_);
v___x_2715_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2714_);
lean_dec_ref(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v___f_2712_);
lean_dec(v_getEnv_2711_);
lean_dec(v_toBind_2710_);
v___x_2716_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2717_ = l_Lean_throwError___redArg(v_inst_2708_, v_inst_2709_, v___x_2716_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; 
lean_dec_ref(v_inst_2709_);
lean_dec_ref(v_inst_2708_);
v___x_2718_ = lean_apply_4(v_toBind_2710_, lean_box(0), lean_box(0), v_getEnv_2711_, v___f_2712_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_docs_2722_, lean_object* v_deferred_2723_){
_start:
{
lean_object* v_toBind_2724_; lean_object* v_getEnv_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___x_2728_; 
v_toBind_2724_ = lean_ctor_get(v_inst_2719_, 1);
lean_inc_n(v_toBind_2724_, 3);
v_getEnv_2725_ = lean_ctor_get(v_inst_2720_, 0);
lean_inc_n(v_getEnv_2725_, 3);
lean_inc_ref(v_inst_2721_);
lean_inc_ref(v_inst_2719_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2726_, 0, v_docs_2722_);
lean_closure_set(v___f_2726_, 1, v_inst_2719_);
lean_closure_set(v___f_2726_, 2, v_inst_2721_);
lean_closure_set(v___f_2726_, 3, v_deferred_2723_);
lean_closure_set(v___f_2726_, 4, v_inst_2720_);
lean_closure_set(v___f_2726_, 5, v_toBind_2724_);
lean_closure_set(v___f_2726_, 6, v_getEnv_2725_);
v___f_2727_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2727_, 0, v_inst_2719_);
lean_closure_set(v___f_2727_, 1, v_inst_2721_);
lean_closure_set(v___f_2727_, 2, v_toBind_2724_);
lean_closure_set(v___f_2727_, 3, v_getEnv_2725_);
lean_closure_set(v___f_2727_, 4, v___f_2726_);
v___x_2728_ = lean_apply_4(v_toBind_2724_, lean_box(0), lean_box(0), v_getEnv_2725_, v___f_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_inst_2733_, lean_object* v_docs_2734_, lean_object* v_deferred_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2730_, v_inst_2731_, v_inst_2733_, v_docs_2734_, v_deferred_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_docs_2742_, lean_object* v_deferred_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_addVersoModDocStringCore(v_m_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_docs_2742_, v_deferred_2743_);
lean_dec(v_inst_2740_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2745_, lean_object* v_as_2746_, size_t v_i_2747_, size_t v_stop_2748_, lean_object* v_b_2749_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_eq(v_i_2747_, v_stop_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v_index_2752_; lean_object* v_sourceString_2753_; lean_object* v_imports_2754_; lean_object* v_currNamespace_2755_; lean_object* v_openDecls_2756_; lean_object* v_options_2757_; lean_object* v_check_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2774_; 
v___x_2751_ = lean_array_uget(v_as_2746_, v_i_2747_);
v_index_2752_ = lean_ctor_get(v___x_2751_, 1);
v_sourceString_2753_ = lean_ctor_get(v___x_2751_, 2);
v_imports_2754_ = lean_ctor_get(v___x_2751_, 3);
v_currNamespace_2755_ = lean_ctor_get(v___x_2751_, 4);
v_openDecls_2756_ = lean_ctor_get(v___x_2751_, 5);
v_options_2757_ = lean_ctor_get(v___x_2751_, 6);
v_check_2758_ = lean_ctor_get(v___x_2751_, 7);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___x_2751_, 0);
lean_dec(v_unused_2775_);
v___x_2760_ = v___x_2751_;
v_isShared_2761_ = v_isSharedCheck_2774_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_check_2758_);
lean_inc(v_options_2757_);
lean_inc(v_openDecls_2756_);
lean_inc(v_currNamespace_2755_);
lean_inc(v_imports_2754_);
lean_inc(v_sourceString_2753_);
lean_inc(v_index_2752_);
lean_dec(v___x_2751_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2774_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v_toEnvExtension_2763_; lean_object* v_asyncMode_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2762_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2763_ = lean_ctor_get(v___x_2762_, 0);
v_asyncMode_2764_ = lean_ctor_get(v_toEnvExtension_2763_, 2);
lean_inc(v_declName_2745_);
v___x_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_declName_2745_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2765_);
v___x_2767_ = v___x_2760_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_index_2752_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_sourceString_2753_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v_imports_2754_);
lean_ctor_set(v_reuseFailAlloc_2773_, 4, v_currNamespace_2755_);
lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_openDecls_2756_);
lean_ctor_set(v_reuseFailAlloc_2773_, 6, v_options_2757_);
lean_ctor_set(v_reuseFailAlloc_2773_, 7, v_check_2758_);
v___x_2767_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; 
v___x_2768_ = lean_box(0);
v___x_2769_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2762_, v_b_2749_, v___x_2767_, v_asyncMode_2764_, v___x_2768_);
v___x_2770_ = ((size_t)1ULL);
v___x_2771_ = lean_usize_add(v_i_2747_, v___x_2770_);
v_i_2747_ = v___x_2771_;
v_b_2749_ = v___x_2769_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2745_);
return v_b_2749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2776_, lean_object* v_as_2777_, lean_object* v_i_2778_, lean_object* v_stop_2779_, lean_object* v_b_2780_){
_start:
{
size_t v_i_boxed_2781_; size_t v_stop_boxed_2782_; lean_object* v_res_2783_; 
v_i_boxed_2781_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_stop_boxed_2782_ = lean_unbox_usize(v_stop_2779_);
lean_dec(v_stop_2779_);
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2776_, v_as_2777_, v_i_boxed_2781_, v_stop_boxed_2782_, v_b_2780_);
lean_dec_ref(v_as_2777_);
return v_res_2783_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2784_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
lean_ctor_set(v___x_2790_, 2, v___x_2789_);
lean_ctor_set(v___x_2790_, 3, v___x_2789_);
lean_ctor_set(v___x_2790_, 4, v___x_2789_);
lean_ctor_set(v___x_2790_, 5, v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2791_, lean_object* v_docs_2792_, lean_object* v_deferred_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2833_; lean_object* v___y_2834_; uint8_t v___x_2852_; 
v___x_2852_ = l_Lean_Name_isAnonymous(v_declName_2791_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; lean_object* v_env_2854_; lean_object* v___x_2855_; 
v___x_2853_ = lean_st_ref_get(v___y_2799_);
v_env_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc_ref(v_env_2854_);
lean_dec(v___x_2853_);
v___x_2855_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2854_, v_declName_2791_);
lean_dec_ref(v_env_2854_);
if (lean_obj_tag(v___x_2855_) == 0)
{
v___y_2833_ = v___y_2797_;
v___y_2834_ = v___y_2799_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2870_; 
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v___x_2855_, 0);
lean_dec(v_unused_2871_);
v___x_2857_ = v___x_2855_;
v_isShared_2858_ = v_isSharedCheck_2870_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v___x_2855_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2870_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
if (v___x_2852_ == 0)
{
lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
lean_dec_ref(v_docs_2792_);
v___x_2859_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2860_ = 1;
v___x_2861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2791_, v___x_2860_);
v___x_2862_ = lean_string_append(v___x_2859_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set_tag(v___x_2857_, 3);
lean_ctor_set(v___x_2857_, 0, v___x_2864_);
v___x_2866_ = v___x_2857_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = l_Lean_MessageData_ofFormat(v___x_2866_);
v___x_2868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2867_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2868_;
}
}
else
{
lean_del_object(v___x_2857_);
v___y_2833_ = v___y_2797_;
v___y_2834_ = v___y_2799_;
goto v___jp_2832_;
}
}
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref(v_docs_2792_);
lean_dec(v_declName_2791_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
v___jp_2801_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_mctx_2816_; lean_object* v_zetaDeltaFVarIds_2817_; lean_object* v_postponed_2818_; lean_object* v_diag_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2830_; 
v___x_2812_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2813_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2813_, 0, v___y_2811_);
lean_ctor_set(v___x_2813_, 1, v___y_2804_);
lean_ctor_set(v___x_2813_, 2, v___y_2808_);
lean_ctor_set(v___x_2813_, 3, v___y_2806_);
lean_ctor_set(v___x_2813_, 4, v___y_2810_);
lean_ctor_set(v___x_2813_, 5, v___x_2812_);
lean_ctor_set(v___x_2813_, 6, v___y_2809_);
lean_ctor_set(v___x_2813_, 7, v___y_2803_);
lean_ctor_set(v___x_2813_, 8, v___y_2807_);
v___x_2814_ = lean_st_ref_put(v___y_2802_, v___x_2813_);
v___x_2815_ = lean_st_ref_take(v___y_2805_);
v_mctx_2816_ = lean_ctor_get(v___x_2815_, 0);
v_zetaDeltaFVarIds_2817_ = lean_ctor_get(v___x_2815_, 2);
v_postponed_2818_ = lean_ctor_get(v___x_2815_, 3);
v_diag_2819_ = lean_ctor_get(v___x_2815_, 4);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2815_, 1);
lean_dec(v_unused_2831_);
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2830_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_diag_2819_);
lean_inc(v_postponed_2818_);
lean_inc(v_zetaDeltaFVarIds_2817_);
lean_inc(v_mctx_2816_);
lean_dec(v___x_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2830_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2823_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 1, v___x_2823_);
v___x_2825_ = v___x_2821_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_mctx_2816_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_zetaDeltaFVarIds_2817_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_postponed_2818_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_diag_2819_);
v___x_2825_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2826_ = lean_st_ref_put(v___y_2805_, v___x_2825_);
v___x_2827_ = lean_box(0);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
return v___x_2828_;
}
}
}
v___jp_2832_:
{
lean_object* v___x_2835_; lean_object* v_env_2836_; lean_object* v_nextMacroScope_2837_; lean_object* v_ngen_2838_; lean_object* v_auxDeclNGen_2839_; lean_object* v_traceState_2840_; lean_object* v_messages_2841_; lean_object* v_infoState_2842_; lean_object* v_snapshotTasks_2843_; lean_object* v___x_2844_; lean_object* v_env_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2835_ = lean_st_ref_take(v___y_2834_);
v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc_ref(v_env_2836_);
v_nextMacroScope_2837_ = lean_ctor_get(v___x_2835_, 1);
lean_inc(v_nextMacroScope_2837_);
v_ngen_2838_ = lean_ctor_get(v___x_2835_, 2);
lean_inc_ref(v_ngen_2838_);
v_auxDeclNGen_2839_ = lean_ctor_get(v___x_2835_, 3);
lean_inc_ref(v_auxDeclNGen_2839_);
v_traceState_2840_ = lean_ctor_get(v___x_2835_, 4);
lean_inc_ref(v_traceState_2840_);
v_messages_2841_ = lean_ctor_get(v___x_2835_, 6);
lean_inc_ref(v_messages_2841_);
v_infoState_2842_ = lean_ctor_get(v___x_2835_, 7);
lean_inc_ref(v_infoState_2842_);
v_snapshotTasks_2843_ = lean_ctor_get(v___x_2835_, 8);
lean_inc_ref(v_snapshotTasks_2843_);
lean_dec(v___x_2835_);
v___x_2844_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2791_);
v_env_2845_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2844_, v_env_2836_, v_declName_2791_, v_docs_2792_);
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = lean_array_get_size(v_deferred_2793_);
v___x_2848_ = lean_nat_dec_lt(v___x_2846_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_dec(v_declName_2791_);
v___y_2802_ = v___y_2834_;
v___y_2803_ = v_infoState_2842_;
v___y_2804_ = v_nextMacroScope_2837_;
v___y_2805_ = v___y_2833_;
v___y_2806_ = v_auxDeclNGen_2839_;
v___y_2807_ = v_snapshotTasks_2843_;
v___y_2808_ = v_ngen_2838_;
v___y_2809_ = v_messages_2841_;
v___y_2810_ = v_traceState_2840_;
v___y_2811_ = v_env_2845_;
goto v___jp_2801_;
}
else
{
size_t v___x_2849_; size_t v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = lean_usize_of_nat(v___x_2847_);
v___x_2851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2791_, v_deferred_2793_, v___x_2849_, v___x_2850_, v_env_2845_);
v___y_2802_ = v___y_2834_;
v___y_2803_ = v_infoState_2842_;
v___y_2804_ = v_nextMacroScope_2837_;
v___y_2805_ = v___y_2833_;
v___y_2806_ = v_auxDeclNGen_2839_;
v___y_2807_ = v_snapshotTasks_2843_;
v___y_2808_ = v_ngen_2838_;
v___y_2809_ = v_messages_2841_;
v___y_2810_ = v_traceState_2840_;
v___y_2811_ = v___x_2851_;
goto v___jp_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2874_, lean_object* v_docs_2875_, lean_object* v_deferred_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2874_, v_docs_2875_, v_deferred_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_deferred_2876_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2885_, lean_object* v_binders_2886_, lean_object* v_docComment_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___x_2915_; lean_object* v_env_2916_; lean_object* v___x_2917_; 
v___x_2915_ = lean_st_ref_get(v_a_2893_);
v_env_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc_ref(v_env_2916_);
lean_dec(v___x_2915_);
v___x_2917_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2916_, v_declName_2885_);
lean_dec_ref(v_env_2916_);
if (lean_obj_tag(v___x_2917_) == 0)
{
v___y_2896_ = v_a_2888_;
v___y_2897_ = v_a_2889_;
v___y_2898_ = v_a_2890_;
v___y_2899_ = v_a_2891_;
v___y_2900_ = v_a_2892_;
v___y_2901_ = v_a_2893_;
goto v___jp_2895_;
}
else
{
lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_docComment_2887_);
lean_dec(v_binders_2886_);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2932_ == 0)
{
lean_object* v_unused_2933_; 
v_unused_2933_ = lean_ctor_get(v___x_2917_, 0);
lean_dec(v_unused_2933_);
v___x_2919_ = v___x_2917_;
v_isShared_2920_ = v_isSharedCheck_2932_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v___x_2917_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2932_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2921_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2922_ = 1;
v___x_2923_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2885_, v___x_2922_);
v___x_2924_ = lean_string_append(v___x_2921_, v___x_2923_);
lean_dec_ref(v___x_2923_);
v___x_2925_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2926_ = lean_string_append(v___x_2924_, v___x_2925_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 3);
lean_ctor_set(v___x_2919_, 0, v___x_2926_);
v___x_2928_ = v___x_2919_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = l_Lean_MessageData_ofFormat(v___x_2928_);
v___x_2930_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2929_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
return v___x_2930_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2902_; 
lean_inc(v_declName_2885_);
v___x_2902_ = l_Lean_versoDocString(v_declName_2885_, v_binders_2886_, v_docComment_2887_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_toVersoDocString_2904_; lean_object* v_deferredChecks_2905_; lean_object* v___x_2906_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v_toVersoDocString_2904_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_toVersoDocString_2904_);
v_deferredChecks_2905_ = lean_ctor_get(v_a_2903_, 1);
lean_inc_ref(v_deferredChecks_2905_);
lean_dec(v_a_2903_);
v___x_2906_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2885_, v_toVersoDocString_2904_, v_deferredChecks_2905_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec_ref(v_deferredChecks_2905_);
return v___x_2906_;
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec(v_declName_2885_);
v_a_2907_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2902_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2902_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2934_, lean_object* v_binders_2935_, lean_object* v_docComment_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Lean_addVersoDocString(v_declName_2934_, v_binders_2935_, v_docComment_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2945_, lean_object* v_docComment_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___x_2974_; lean_object* v_env_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_st_ref_get(v_a_2952_);
v_env_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc_ref(v_env_2975_);
lean_dec(v___x_2974_);
v___x_2976_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2975_, v_declName_2945_);
lean_dec_ref(v_env_2975_);
if (lean_obj_tag(v___x_2976_) == 0)
{
v___y_2955_ = v_a_2947_;
v___y_2956_ = v_a_2948_;
v___y_2957_ = v_a_2949_;
v___y_2958_ = v_a_2950_;
v___y_2959_ = v_a_2951_;
v___y_2960_ = v_a_2952_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v_docComment_2946_);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2976_, 0);
lean_dec(v_unused_2992_);
v___x_2978_ = v___x_2976_;
v_isShared_2979_ = v_isSharedCheck_2991_;
goto v_resetjp_2977_;
}
else
{
lean_dec(v___x_2976_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2991_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2980_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2981_ = 1;
v___x_2982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2945_, v___x_2981_);
v___x_2983_ = lean_string_append(v___x_2980_, v___x_2982_);
lean_dec_ref(v___x_2982_);
v___x_2984_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2985_ = lean_string_append(v___x_2983_, v___x_2984_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 3);
lean_ctor_set(v___x_2978_, 0, v___x_2985_);
v___x_2987_ = v___x_2978_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = l_Lean_MessageData_ofFormat(v___x_2987_);
v___x_2989_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2988_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
return v___x_2989_;
}
}
}
v___jp_2954_:
{
lean_object* v___x_2961_; 
lean_inc(v_declName_2945_);
v___x_2961_ = l_Lean_versoDocStringFromString(v_declName_2945_, v_docComment_2946_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_toVersoDocString_2963_; lean_object* v_deferredChecks_2964_; lean_object* v___x_2965_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v_toVersoDocString_2963_ = lean_ctor_get(v_a_2962_, 0);
lean_inc_ref(v_toVersoDocString_2963_);
v_deferredChecks_2964_ = lean_ctor_get(v_a_2962_, 1);
lean_inc_ref(v_deferredChecks_2964_);
lean_dec(v_a_2962_);
v___x_2965_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2945_, v_toVersoDocString_2963_, v_deferredChecks_2964_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
lean_dec_ref(v_deferredChecks_2964_);
return v___x_2965_;
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v_declName_2945_);
v_a_2966_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2961_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2961_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2993_, lean_object* v_docComment_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l_Lean_addVersoDocStringFromString(v_declName_2993_, v_docComment_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
lean_dec(v_a_3000_);
lean_dec_ref(v_a_2999_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3003_, lean_object* v_msgData_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = 2;
v___x_3011_ = 0;
v___x_3012_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_3003_, v_msgData_3004_, v___x_3010_, v___x_3011_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3013_, lean_object* v_msgData_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3013_, v_msgData_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v_ref_3013_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3021_, lean_object* v_str_3022_, lean_object* v_as_3023_, size_t v_sz_3024_, size_t v_i_3025_, lean_object* v_b_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_a_3035_; uint8_t v___x_3039_; 
v___x_3039_ = lean_usize_dec_lt(v_i_3025_, v_sz_3024_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_b_3026_);
return v___x_3040_;
}
else
{
lean_object* v_a_3041_; lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v_start_3044_; lean_object* v_stop_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3065_; 
v_a_3041_ = lean_array_uget_borrowed(v_as_3023_, v_i_3025_);
v_fst_3042_ = lean_ctor_get(v_a_3041_, 0);
lean_inc(v_fst_3042_);
v_snd_3043_ = lean_ctor_get(v_a_3041_, 1);
v_start_3044_ = lean_ctor_get(v_fst_3042_, 0);
v_stop_3045_ = lean_ctor_get(v_fst_3042_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_fst_3042_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3047_ = v_fst_3042_;
v_isShared_3048_ = v_isSharedCheck_3065_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_stop_3045_);
lean_inc(v_start_3044_);
lean_dec(v_fst_3042_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3065_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_box(0);
if (lean_obj_tag(v___y_3021_) == 1)
{
lean_object* v_val_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_val_3050_ = lean_ctor_get(v___y_3021_, 0);
v___x_3051_ = lean_nat_add(v_val_3050_, v_start_3044_);
v___x_3052_ = lean_nat_add(v_val_3050_, v_stop_3045_);
v___x_3053_ = 0;
v___x_3054_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3054_, 0, v___x_3051_);
lean_ctor_set(v___x_3054_, 1, v___x_3052_);
lean_ctor_set_uint8(v___x_3054_, sizeof(void*)*2, v___x_3053_);
v___x_3055_ = lean_string_utf8_extract(v_str_3022_, v_start_3044_, v_stop_3045_);
lean_dec(v_stop_3045_);
lean_dec(v_start_3044_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set_tag(v___x_3047_, 2);
lean_ctor_set(v___x_3047_, 1, v___x_3055_);
lean_ctor_set(v___x_3047_, 0, v___x_3054_);
v___x_3057_ = v___x_3047_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
lean_inc(v_snd_3043_);
v___x_3058_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3058_, 0, v_snd_3043_);
v___x_3059_ = l_Lean_MessageData_ofFormat(v___x_3058_);
v___x_3060_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3057_, v___x_3059_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec_ref(v___x_3057_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
v_a_3035_ = v___x_3049_;
goto v___jp_3034_;
}
else
{
return v___x_3060_;
}
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_del_object(v___x_3047_);
lean_dec(v_stop_3045_);
lean_dec(v_start_3044_);
lean_inc(v_snd_3043_);
v___x_3062_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3062_, 0, v_snd_3043_);
v___x_3063_ = l_Lean_MessageData_ofFormat(v___x_3062_);
v___x_3064_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3063_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref_known(v___x_3064_, 1);
v_a_3035_ = v___x_3049_;
goto v___jp_3034_;
}
else
{
return v___x_3064_;
}
}
}
}
v___jp_3034_:
{
size_t v___x_3036_; size_t v___x_3037_; 
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_add(v_i_3025_, v___x_3036_);
v_i_3025_ = v___x_3037_;
v_b_3026_ = v_a_3035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3066_, lean_object* v_str_3067_, lean_object* v_as_3068_, lean_object* v_sz_3069_, lean_object* v_i_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
size_t v_sz_boxed_3079_; size_t v_i_boxed_3080_; lean_object* v_res_3081_; 
v_sz_boxed_3079_ = lean_unbox_usize(v_sz_3069_);
lean_dec(v_sz_3069_);
v_i_boxed_3080_ = lean_unbox_usize(v_i_3070_);
lean_dec(v_i_3070_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3066_, v_str_3067_, v_as_3068_, v_sz_boxed_3079_, v_i_boxed_3080_, v_b_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec_ref(v_as_3068_);
lean_dec_ref(v_str_3067_);
lean_dec(v___y_3066_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_str_3090_; lean_object* v___y_3092_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_str_3090_ = l_Lean_TSyntax_getDocString(v_docstring_3082_);
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = l_Lean_Syntax_getArg(v_docstring_3082_, v___x_3107_);
v___x_3109_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3108_);
lean_dec(v___x_3108_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_box(0);
v___y_3092_ = v___x_3110_;
goto v___jp_3091_;
}
else
{
lean_object* v_val_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; 
v_val_3111_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3112_ = 0;
v___x_3113_ = l_Lean_SourceInfo_getPos_x3f(v_val_3111_, v___x_3112_);
lean_dec(v_val_3111_);
v___y_3092_ = v___x_3113_;
goto v___jp_3091_;
}
v___jp_3091_:
{
lean_object* v___x_3093_; lean_object* v_fst_3094_; lean_object* v___x_3095_; size_t v_sz_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
lean_inc_ref(v_str_3090_);
v___x_3093_ = l_Lean_rewriteManualLinksCore(v_str_3090_);
v_fst_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_fst_3094_);
lean_dec_ref(v___x_3093_);
v___x_3095_ = lean_box(0);
v_sz_3096_ = lean_array_size(v_fst_3094_);
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3092_, v_str_3090_, v_fst_3094_, v_sz_3096_, v___x_3097_, v___x_3095_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v_fst_3094_);
lean_dec_ref(v_str_3090_);
lean_dec(v___y_3092_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; 
v_unused_3106_ = lean_ctor_get(v___x_3098_, 0);
lean_dec(v_unused_3106_);
v___x_3100_ = v___x_3098_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_dec(v___x_3098_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v___x_3095_);
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3095_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
else
{
return v___x_3098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v_docstring_3114_);
return v_res_3122_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3125_ = l_Lean_stringToMessageData(v___x_3124_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_val_3141_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = l_Lean_Syntax_getArg(v_stx_3126_, v___x_3148_);
switch(lean_obj_tag(v___x_3149_))
{
case 2:
{
lean_object* v_val_3150_; 
lean_dec(v_stx_3126_);
v_val_3150_ = lean_ctor_get(v___x_3149_, 1);
lean_inc_ref(v_val_3150_);
lean_dec_ref_known(v___x_3149_, 2);
v_val_3141_ = v_val_3150_;
goto v___jp_3140_;
}
case 1:
{
lean_object* v_kind_3151_; 
v_kind_3151_ = lean_ctor_get(v___x_3149_, 1);
lean_inc(v_kind_3151_);
if (lean_obj_tag(v_kind_3151_) == 1)
{
lean_object* v_pre_3152_; 
v_pre_3152_ = lean_ctor_get(v_kind_3151_, 0);
lean_inc(v_pre_3152_);
if (lean_obj_tag(v_pre_3152_) == 1)
{
lean_object* v_pre_3153_; 
v_pre_3153_ = lean_ctor_get(v_pre_3152_, 0);
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
if (lean_obj_tag(v_pre_3155_) == 0)
{
lean_object* v_str_3156_; lean_object* v_str_3157_; lean_object* v_str_3158_; lean_object* v_str_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v_str_3156_ = lean_ctor_get(v_kind_3151_, 1);
lean_inc_ref(v_str_3156_);
lean_dec_ref_known(v_kind_3151_, 2);
v_str_3157_ = lean_ctor_get(v_pre_3152_, 1);
lean_inc_ref(v_str_3157_);
lean_dec_ref_known(v_pre_3152_, 2);
v_str_3158_ = lean_ctor_get(v_pre_3153_, 1);
lean_inc_ref(v_str_3158_);
lean_dec_ref_known(v_pre_3153_, 2);
v_str_3159_ = lean_ctor_get(v_pre_3154_, 1);
lean_inc_ref(v_str_3159_);
lean_dec_ref_known(v_pre_3154_, 2);
v___x_3160_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3161_ = lean_string_dec_eq(v_str_3159_, v___x_3160_);
lean_dec_ref(v_str_3159_);
if (v___x_3161_ == 0)
{
lean_dec_ref(v_str_3158_);
lean_dec_ref(v_str_3157_);
lean_dec_ref(v_str_3156_);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
else
{
lean_object* v___x_3162_; uint8_t v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3163_ = lean_string_dec_eq(v_str_3158_, v___x_3162_);
lean_dec_ref(v_str_3158_);
if (v___x_3163_ == 0)
{
lean_dec_ref(v_str_3157_);
lean_dec_ref(v_str_3156_);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
else
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3165_ = lean_string_dec_eq(v_str_3157_, v___x_3164_);
lean_dec_ref(v_str_3157_);
if (v___x_3165_ == 0)
{
lean_dec_ref(v_str_3156_);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
else
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3167_ = lean_string_dec_eq(v_str_3156_, v___x_3166_);
lean_dec_ref(v_str_3156_);
if (v___x_3167_ == 0)
{
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_unsigned_to_nat(0u);
v___x_3169_ = l_Lean_Syntax_getArg(v___x_3149_, v___x_3168_);
lean_dec_ref_known(v___x_3149_, 3);
if (lean_obj_tag(v___x_3169_) == 2)
{
lean_object* v_val_3170_; 
lean_dec(v_stx_3126_);
v_val_3170_ = lean_ctor_get(v___x_3169_, 1);
lean_inc_ref(v_val_3170_);
lean_dec_ref_known(v___x_3169_, 2);
v_val_3141_ = v_val_3170_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_dec(v___x_3169_);
v___x_3171_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3126_);
v___x_3172_ = l_Lean_MessageData_ofSyntax(v_stx_3126_);
v___x_3173_ = l_Lean_indentD(v___x_3172_);
v___x_3174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3126_, v___x_3174_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v_stx_3126_);
return v___x_3175_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3154_, 2);
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec_ref_known(v_pre_3152_, 2);
lean_dec_ref_known(v_kind_3151_, 2);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
}
else
{
lean_dec(v_pre_3154_);
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec_ref_known(v_pre_3152_, 2);
lean_dec_ref_known(v_kind_3151_, 2);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
}
else
{
lean_dec_ref_known(v_pre_3152_, 2);
lean_dec(v_pre_3153_);
lean_dec_ref_known(v_kind_3151_, 2);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
}
else
{
lean_dec_ref_known(v_kind_3151_, 2);
lean_dec(v_pre_3152_);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
}
else
{
lean_dec(v_kind_3151_);
lean_dec_ref_known(v___x_3149_, 3);
goto v___jp_3134_;
}
}
default: 
{
lean_dec(v___x_3149_);
goto v___jp_3134_;
}
}
v___jp_3134_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3135_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3126_);
v___x_3136_ = l_Lean_MessageData_ofSyntax(v_stx_3126_);
v___x_3137_ = l_Lean_indentD(v___x_3136_);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3135_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3126_, v___x_3138_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v_stx_3126_);
return v___x_3139_;
}
v___jp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_string_utf8_byte_size(v_val_3141_);
v___x_3144_ = lean_unsigned_to_nat(2u);
v___x_3145_ = lean_nat_sub(v___x_3143_, v___x_3144_);
v___x_3146_ = lean_string_utf8_extract(v_val_3141_, v___x_3142_, v___x_3145_);
lean_dec(v___x_3145_);
lean_dec_ref(v_val_3141_);
v___x_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
return v___x_3147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3185_, lean_object* v_docComment_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_Name_isAnonymous(v_declName_3185_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v_env_3259_; lean_object* v___x_3260_; 
v___x_3258_ = lean_st_ref_get(v___y_3192_);
v_env_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3258_);
v___x_3260_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3259_, v_declName_3185_);
lean_dec_ref(v_env_3259_);
if (lean_obj_tag(v___x_3260_) == 0)
{
v___y_3195_ = v___y_3187_;
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
v___y_3200_ = v___y_3192_;
goto v___jp_3194_;
}
else
{
lean_dec_ref_known(v___x_3260_, 1);
if (v___x_3257_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v_docComment_3186_);
v___x_3261_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3262_ = l_Lean_MessageData_ofConstName(v_declName_3185_, v___x_3257_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3265_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3266_;
}
else
{
v___y_3195_ = v___y_3187_;
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
v___y_3200_ = v___y_3192_;
goto v___jp_3194_;
}
}
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
lean_dec(v_docComment_3186_);
lean_dec(v_declName_3185_);
v___x_3267_ = lean_box(0);
v___x_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
return v___x_3268_;
}
v___jp_3194_:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3186_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v___x_3202_; 
lean_dec_ref_known(v___x_3201_, 1);
v___x_3202_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3186_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3248_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3248_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3248_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v_env_3208_; lean_object* v_nextMacroScope_3209_; lean_object* v_ngen_3210_; lean_object* v_auxDeclNGen_3211_; lean_object* v_traceState_3212_; lean_object* v_messages_3213_; lean_object* v_infoState_3214_; lean_object* v_snapshotTasks_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3246_; 
v___x_3207_ = lean_st_ref_take(v___y_3200_);
v_env_3208_ = lean_ctor_get(v___x_3207_, 0);
v_nextMacroScope_3209_ = lean_ctor_get(v___x_3207_, 1);
v_ngen_3210_ = lean_ctor_get(v___x_3207_, 2);
v_auxDeclNGen_3211_ = lean_ctor_get(v___x_3207_, 3);
v_traceState_3212_ = lean_ctor_get(v___x_3207_, 4);
v_messages_3213_ = lean_ctor_get(v___x_3207_, 6);
v_infoState_3214_ = lean_ctor_get(v___x_3207_, 7);
v_snapshotTasks_3215_ = lean_ctor_get(v___x_3207_, 8);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v___x_3207_, 5);
lean_dec(v_unused_3247_);
v___x_3217_ = v___x_3207_;
v_isShared_3218_ = v_isSharedCheck_3246_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_snapshotTasks_3215_);
lean_inc(v_infoState_3214_);
lean_inc(v_messages_3213_);
lean_inc(v_traceState_3212_);
lean_inc(v_auxDeclNGen_3211_);
lean_inc(v_ngen_3210_);
lean_inc(v_nextMacroScope_3209_);
lean_inc(v_env_3208_);
lean_dec(v___x_3207_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3246_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3219_ = l_Lean_docStringExt;
v___x_3220_ = l_String_removeLeadingSpaces(v_a_3203_);
v___x_3221_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3219_, v_env_3208_, v_declName_3185_, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 5, v___x_3222_);
lean_ctor_set(v___x_3217_, 0, v___x_3221_);
v___x_3224_ = v___x_3217_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_nextMacroScope_3209_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_ngen_3210_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_auxDeclNGen_3211_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v_traceState_3212_);
lean_ctor_set(v_reuseFailAlloc_3245_, 5, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3245_, 6, v_messages_3213_);
lean_ctor_set(v_reuseFailAlloc_3245_, 7, v_infoState_3214_);
lean_ctor_set(v_reuseFailAlloc_3245_, 8, v_snapshotTasks_3215_);
v___x_3224_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_mctx_3227_; lean_object* v_zetaDeltaFVarIds_3228_; lean_object* v_postponed_3229_; lean_object* v_diag_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3243_; 
v___x_3225_ = lean_st_ref_put(v___y_3200_, v___x_3224_);
v___x_3226_ = lean_st_ref_take(v___y_3198_);
v_mctx_3227_ = lean_ctor_get(v___x_3226_, 0);
v_zetaDeltaFVarIds_3228_ = lean_ctor_get(v___x_3226_, 2);
v_postponed_3229_ = lean_ctor_get(v___x_3226_, 3);
v_diag_3230_ = lean_ctor_get(v___x_3226_, 4);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3226_, 1);
lean_dec(v_unused_3244_);
v___x_3232_ = v___x_3226_;
v_isShared_3233_ = v_isSharedCheck_3243_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_diag_3230_);
lean_inc(v_postponed_3229_);
lean_inc(v_zetaDeltaFVarIds_3228_);
lean_inc(v_mctx_3227_);
lean_dec(v___x_3226_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3243_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3234_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 1, v___x_3234_);
v___x_3236_ = v___x_3232_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_mctx_3227_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v_zetaDeltaFVarIds_3228_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v_postponed_3229_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v_diag_3230_);
v___x_3236_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3237_ = lean_st_ref_put(v___y_3198_, v___x_3236_);
v___x_3238_ = lean_box(0);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3238_);
v___x_3240_ = v___x_3205_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_declName_3185_);
v_a_3249_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3202_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3202_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_dec(v_docComment_3186_);
lean_dec(v_declName_3185_);
return v___x_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3269_, lean_object* v_docComment_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3269_, v_docComment_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3279_, lean_object* v_declName_3280_, lean_object* v_binders_3281_, lean_object* v_docComment_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
if (v_isVerso_3279_ == 0)
{
lean_object* v___x_3290_; 
lean_dec(v_binders_3281_);
v___x_3290_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3280_, v_docComment_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
return v___x_3290_;
}
else
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_addVersoDocString(v_declName_3280_, v_binders_3281_, v_docComment_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3292_, lean_object* v_declName_3293_, lean_object* v_binders_3294_, lean_object* v_docComment_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
uint8_t v_isVerso_boxed_3303_; lean_object* v_res_3304_; 
v_isVerso_boxed_3303_ = lean_unbox(v_isVerso_3292_);
v_res_3304_ = l_Lean_addDocStringOf(v_isVerso_boxed_3303_, v_declName_3293_, v_binders_3294_, v_docComment_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3305_, lean_object* v_msgData_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3305_, v_msgData_3306_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3315_, lean_object* v_msgData_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3315_, v_msgData_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v_ref_3315_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3325_, lean_object* v_t_3326_){
_start:
{
if (lean_obj_tag(v_t_3326_) == 0)
{
lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v_l_3329_; lean_object* v_r_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3984_; 
v_k_3327_ = lean_ctor_get(v_t_3326_, 1);
v_v_3328_ = lean_ctor_get(v_t_3326_, 2);
v_l_3329_ = lean_ctor_get(v_t_3326_, 3);
v_r_3330_ = lean_ctor_get(v_t_3326_, 4);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_t_3326_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v_t_3326_, 0);
lean_dec(v_unused_3985_);
v___x_3332_ = v_t_3326_;
v_isShared_3333_ = v_isSharedCheck_3984_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_r_3330_);
lean_inc(v_l_3329_);
lean_inc(v_v_3328_);
lean_inc(v_k_3327_);
lean_dec(v_t_3326_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3984_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
uint8_t v___x_3334_; 
v___x_3334_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3325_, v_k_3327_);
switch(v___x_3334_)
{
case 0:
{
lean_object* v_impl_3335_; lean_object* v___x_3336_; 
v_impl_3335_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3325_, v_l_3329_);
v___x_3336_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3335_) == 0)
{
if (lean_obj_tag(v_r_3330_) == 0)
{
lean_object* v_size_3337_; lean_object* v_size_3338_; lean_object* v_k_3339_; lean_object* v_v_3340_; lean_object* v_l_3341_; lean_object* v_r_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_size_3337_ = lean_ctor_get(v_impl_3335_, 0);
lean_inc(v_size_3337_);
v_size_3338_ = lean_ctor_get(v_r_3330_, 0);
v_k_3339_ = lean_ctor_get(v_r_3330_, 1);
v_v_3340_ = lean_ctor_get(v_r_3330_, 2);
v_l_3341_ = lean_ctor_get(v_r_3330_, 3);
lean_inc(v_l_3341_);
v_r_3342_ = lean_ctor_get(v_r_3330_, 4);
v___x_3343_ = lean_unsigned_to_nat(3u);
v___x_3344_ = lean_nat_mul(v___x_3343_, v_size_3337_);
v___x_3345_ = lean_nat_dec_lt(v___x_3344_, v_size_3338_);
lean_dec(v___x_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
lean_dec(v_l_3341_);
v___x_3346_ = lean_nat_add(v___x_3336_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3347_ = lean_nat_add(v___x_3346_, v_size_3338_);
lean_dec(v___x_3346_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 3, v_impl_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3347_);
v___x_3349_ = v___x_3332_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_impl_3335_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_r_3330_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
else
{
lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3414_; 
lean_inc(v_r_3342_);
lean_inc(v_v_3340_);
lean_inc(v_k_3339_);
lean_inc(v_size_3338_);
v_isSharedCheck_3414_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; lean_object* v_unused_3416_; lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3415_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3415_);
v_unused_3416_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3416_);
v_unused_3417_ = lean_ctor_get(v_r_3330_, 2);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_r_3330_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3419_);
v___x_3352_ = v_r_3330_;
v_isShared_3353_ = v_isSharedCheck_3414_;
goto v_resetjp_3351_;
}
else
{
lean_dec(v_r_3330_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3414_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_size_3354_; lean_object* v_k_3355_; lean_object* v_v_3356_; lean_object* v_l_3357_; lean_object* v_r_3358_; lean_object* v_size_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_size_3354_ = lean_ctor_get(v_l_3341_, 0);
v_k_3355_ = lean_ctor_get(v_l_3341_, 1);
v_v_3356_ = lean_ctor_get(v_l_3341_, 2);
v_l_3357_ = lean_ctor_get(v_l_3341_, 3);
v_r_3358_ = lean_ctor_get(v_l_3341_, 4);
v_size_3359_ = lean_ctor_get(v_r_3342_, 0);
v___x_3360_ = lean_unsigned_to_nat(2u);
v___x_3361_ = lean_nat_mul(v___x_3360_, v_size_3359_);
v___x_3362_ = lean_nat_dec_lt(v_size_3354_, v___x_3361_);
lean_dec(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3390_; 
lean_inc(v_r_3358_);
lean_inc(v_l_3357_);
lean_inc(v_v_3356_);
lean_inc(v_k_3355_);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_l_3341_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; lean_object* v_unused_3395_; 
v_unused_3391_ = lean_ctor_get(v_l_3341_, 4);
lean_dec(v_unused_3391_);
v_unused_3392_ = lean_ctor_get(v_l_3341_, 3);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_l_3341_, 2);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_l_3341_, 1);
lean_dec(v_unused_3394_);
v_unused_3395_ = lean_ctor_get(v_l_3341_, 0);
lean_dec(v_unused_3395_);
v___x_3364_ = v_l_3341_;
v_isShared_3365_ = v_isSharedCheck_3390_;
goto v_resetjp_3363_;
}
else
{
lean_dec(v_l_3341_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3390_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3380_; 
v___x_3366_ = lean_nat_add(v___x_3336_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3367_ = lean_nat_add(v___x_3366_, v_size_3338_);
lean_dec(v_size_3338_);
if (lean_obj_tag(v_l_3357_) == 0)
{
lean_object* v_size_3388_; 
v_size_3388_ = lean_ctor_get(v_l_3357_, 0);
lean_inc(v_size_3388_);
v___y_3380_ = v_size_3388_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3389_; 
v___x_3389_ = lean_unsigned_to_nat(0u);
v___y_3380_ = v___x_3389_;
goto v___jp_3379_;
}
v___jp_3368_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_nat_add(v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec(v___y_3370_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 4, v_r_3342_);
lean_ctor_set(v___x_3364_, 3, v_r_3358_);
lean_ctor_set(v___x_3364_, 2, v_v_3340_);
lean_ctor_set(v___x_3364_, 1, v_k_3339_);
lean_ctor_set(v___x_3364_, 0, v___x_3372_);
v___x_3374_ = v___x_3364_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3339_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3340_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_r_3358_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_r_3342_);
v___x_3374_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3376_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v___x_3374_);
lean_ctor_set(v___x_3352_, 3, v___y_3369_);
lean_ctor_set(v___x_3352_, 2, v_v_3356_);
lean_ctor_set(v___x_3352_, 1, v_k_3355_);
lean_ctor_set(v___x_3352_, 0, v___x_3367_);
v___x_3376_ = v___x_3352_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3355_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3356_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v___y_3369_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
v___jp_3379_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_nat_add(v___x_3366_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec(v___x_3366_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3357_);
lean_ctor_set(v___x_3332_, 3, v_impl_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3381_);
v___x_3383_ = v___x_3332_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3387_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3387_, 3, v_impl_3335_);
lean_ctor_set(v_reuseFailAlloc_3387_, 4, v_l_3357_);
v___x_3383_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; 
v___x_3384_ = lean_nat_add(v___x_3336_, v_size_3359_);
if (lean_obj_tag(v_r_3358_) == 0)
{
lean_object* v_size_3385_; 
v_size_3385_ = lean_ctor_get(v_r_3358_, 0);
lean_inc(v_size_3385_);
v___y_3369_ = v___x_3383_;
v___y_3370_ = v___x_3384_;
v___y_3371_ = v_size_3385_;
goto v___jp_3368_;
}
else
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_unsigned_to_nat(0u);
v___y_3369_ = v___x_3383_;
v___y_3370_ = v___x_3384_;
v___y_3371_ = v___x_3386_;
goto v___jp_3368_;
}
}
}
}
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_del_object(v___x_3332_);
v___x_3396_ = lean_nat_add(v___x_3336_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3397_ = lean_nat_add(v___x_3396_, v_size_3338_);
lean_dec(v_size_3338_);
v___x_3398_ = lean_nat_add(v___x_3396_, v_size_3354_);
lean_dec(v___x_3396_);
lean_inc_ref(v_impl_3335_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v_l_3341_);
lean_ctor_set(v___x_3352_, 3, v_impl_3335_);
lean_ctor_set(v___x_3352_, 2, v_v_3328_);
lean_ctor_set(v___x_3352_, 1, v_k_3327_);
lean_ctor_set(v___x_3352_, 0, v___x_3398_);
v___x_3400_ = v___x_3352_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_impl_3335_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v_l_3341_);
v___x_3400_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v_impl_3335_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; 
v_unused_3408_ = lean_ctor_get(v_impl_3335_, 4);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_impl_3335_, 3);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_impl_3335_, 2);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_impl_3335_, 1);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_impl_3335_, 0);
lean_dec(v_unused_3412_);
v___x_3402_ = v_impl_3335_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v_impl_3335_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 4, v_r_3342_);
lean_ctor_set(v___x_3402_, 3, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v_v_3340_);
lean_ctor_set(v___x_3402_, 1, v_k_3339_);
lean_ctor_set(v___x_3402_, 0, v___x_3397_);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_k_3339_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_v_3340_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v_r_3342_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v_size_3420_ = lean_ctor_get(v_impl_3335_, 0);
lean_inc(v_size_3420_);
v___x_3421_ = lean_nat_add(v___x_3336_, v_size_3420_);
lean_dec(v_size_3420_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 3, v_impl_3335_);
lean_ctor_set(v___x_3332_, 0, v___x_3421_);
v___x_3423_ = v___x_3332_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_impl_3335_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_r_3330_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
if (lean_obj_tag(v_r_3330_) == 0)
{
lean_object* v_l_3425_; 
v_l_3425_ = lean_ctor_get(v_r_3330_, 3);
lean_inc(v_l_3425_);
if (lean_obj_tag(v_l_3425_) == 0)
{
lean_object* v_r_3426_; 
v_r_3426_ = lean_ctor_get(v_r_3330_, 4);
lean_inc(v_r_3426_);
if (lean_obj_tag(v_r_3426_) == 0)
{
lean_object* v_size_3427_; lean_object* v_k_3428_; lean_object* v_v_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3442_; 
v_size_3427_ = lean_ctor_get(v_r_3330_, 0);
v_k_3428_ = lean_ctor_get(v_r_3330_, 1);
v_v_3429_ = lean_ctor_get(v_r_3330_, 2);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; lean_object* v_unused_3444_; 
v_unused_3443_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3444_);
v___x_3431_ = v_r_3330_;
v_isShared_3432_ = v_isSharedCheck_3442_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_v_3429_);
lean_inc(v_k_3428_);
lean_inc(v_size_3427_);
lean_dec(v_r_3330_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3442_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_size_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3437_; 
v_size_3433_ = lean_ctor_get(v_l_3425_, 0);
v___x_3434_ = lean_nat_add(v___x_3336_, v_size_3427_);
lean_dec(v_size_3427_);
v___x_3435_ = lean_nat_add(v___x_3336_, v_size_3433_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 4, v_l_3425_);
lean_ctor_set(v___x_3431_, 3, v_impl_3335_);
lean_ctor_set(v___x_3431_, 2, v_v_3328_);
lean_ctor_set(v___x_3431_, 1, v_k_3327_);
lean_ctor_set(v___x_3431_, 0, v___x_3435_);
v___x_3437_ = v___x_3431_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3441_, 3, v_impl_3335_);
lean_ctor_set(v_reuseFailAlloc_3441_, 4, v_l_3425_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3426_);
lean_ctor_set(v___x_3332_, 3, v___x_3437_);
lean_ctor_set(v___x_3332_, 2, v_v_3429_);
lean_ctor_set(v___x_3332_, 1, v_k_3428_);
lean_ctor_set(v___x_3332_, 0, v___x_3434_);
v___x_3439_ = v___x_3332_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3428_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3429_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v___x_3437_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_r_3426_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
lean_object* v_k_3445_; lean_object* v_v_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3469_; 
v_k_3445_ = lean_ctor_get(v_r_3330_, 1);
v_v_3446_ = lean_ctor_get(v_r_3330_, 2);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; lean_object* v_unused_3471_; lean_object* v_unused_3472_; 
v_unused_3470_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3471_);
v_unused_3472_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3472_);
v___x_3448_ = v_r_3330_;
v_isShared_3449_ = v_isSharedCheck_3469_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_v_3446_);
lean_inc(v_k_3445_);
lean_dec(v_r_3330_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3469_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_k_3450_; lean_object* v_v_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3465_; 
v_k_3450_ = lean_ctor_get(v_l_3425_, 1);
v_v_3451_ = lean_ctor_get(v_l_3425_, 2);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_l_3425_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3466_ = lean_ctor_get(v_l_3425_, 4);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_l_3425_, 3);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_l_3425_, 0);
lean_dec(v_unused_3468_);
v___x_3453_ = v_l_3425_;
v_isShared_3454_ = v_isSharedCheck_3465_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_v_3451_);
lean_inc(v_k_3450_);
lean_dec(v_l_3425_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3465_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3455_ = lean_unsigned_to_nat(3u);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 4, v_r_3426_);
lean_ctor_set(v___x_3453_, 3, v_r_3426_);
lean_ctor_set(v___x_3453_, 2, v_v_3328_);
lean_ctor_set(v___x_3453_, 1, v_k_3327_);
lean_ctor_set(v___x_3453_, 0, v___x_3336_);
v___x_3457_ = v___x_3453_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_r_3426_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_r_3426_);
v___x_3457_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3459_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 3, v_r_3426_);
lean_ctor_set(v___x_3448_, 0, v___x_3336_);
v___x_3459_ = v___x_3448_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3445_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3446_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_r_3426_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_r_3426_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3459_);
lean_ctor_set(v___x_3332_, 3, v___x_3457_);
lean_ctor_set(v___x_3332_, 2, v_v_3451_);
lean_ctor_set(v___x_3332_, 1, v_k_3450_);
lean_ctor_set(v___x_3332_, 0, v___x_3455_);
v___x_3461_ = v___x_3332_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_k_3450_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_v_3451_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3473_; 
v_r_3473_ = lean_ctor_get(v_r_3330_, 4);
lean_inc(v_r_3473_);
if (lean_obj_tag(v_r_3473_) == 0)
{
lean_object* v_k_3474_; lean_object* v_v_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3486_; 
v_k_3474_ = lean_ctor_get(v_r_3330_, 1);
v_v_3475_ = lean_ctor_get(v_r_3330_, 2);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3487_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3489_);
v___x_3477_ = v_r_3330_;
v_isShared_3478_ = v_isSharedCheck_3486_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_v_3475_);
lean_inc(v_k_3474_);
lean_dec(v_r_3330_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3486_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = lean_unsigned_to_nat(3u);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 4, v_l_3425_);
lean_ctor_set(v___x_3477_, 2, v_v_3328_);
lean_ctor_set(v___x_3477_, 1, v_k_3327_);
lean_ctor_set(v___x_3477_, 0, v___x_3336_);
v___x_3481_ = v___x_3477_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_l_3425_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_l_3425_);
v___x_3481_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3483_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3473_);
lean_ctor_set(v___x_3332_, 3, v___x_3481_);
lean_ctor_set(v___x_3332_, 2, v_v_3475_);
lean_ctor_set(v___x_3332_, 1, v_k_3474_);
lean_ctor_set(v___x_3332_, 0, v___x_3479_);
v___x_3483_ = v___x_3332_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_k_3474_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_v_3475_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_r_3473_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v_size_3490_; lean_object* v_k_3491_; lean_object* v_v_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3503_; 
v_size_3490_ = lean_ctor_get(v_r_3330_, 0);
v_k_3491_ = lean_ctor_get(v_r_3330_, 1);
v_v_3492_ = lean_ctor_get(v_r_3330_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; lean_object* v_unused_3505_; 
v_unused_3504_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3504_);
v_unused_3505_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3505_);
v___x_3494_ = v_r_3330_;
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_v_3492_);
lean_inc(v_k_3491_);
lean_inc(v_size_3490_);
lean_dec(v_r_3330_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3503_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 3, v_r_3473_);
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_size_3490_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_k_3491_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_v_3492_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_r_3473_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_r_3473_);
v___x_3497_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = lean_unsigned_to_nat(2u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3497_);
lean_ctor_set(v___x_3332_, 3, v_r_3473_);
lean_ctor_set(v___x_3332_, 0, v___x_3498_);
v___x_3500_ = v___x_3332_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_r_3473_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v___x_3497_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
else
{
lean_object* v___x_3507_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 3, v_r_3330_);
lean_ctor_set(v___x_3332_, 0, v___x_3336_);
v___x_3507_ = v___x_3332_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_r_3330_);
lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3330_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3332_);
lean_dec(v_v_3328_);
lean_dec(v_k_3327_);
if (lean_obj_tag(v_l_3329_) == 0)
{
if (lean_obj_tag(v_r_3330_) == 0)
{
lean_object* v_size_3509_; lean_object* v_k_3510_; lean_object* v_v_3511_; lean_object* v_l_3512_; lean_object* v_r_3513_; lean_object* v_size_3514_; lean_object* v_k_3515_; lean_object* v_v_3516_; lean_object* v_l_3517_; lean_object* v_r_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v_size_3509_ = lean_ctor_get(v_l_3329_, 0);
v_k_3510_ = lean_ctor_get(v_l_3329_, 1);
v_v_3511_ = lean_ctor_get(v_l_3329_, 2);
v_l_3512_ = lean_ctor_get(v_l_3329_, 3);
v_r_3513_ = lean_ctor_get(v_l_3329_, 4);
lean_inc(v_r_3513_);
v_size_3514_ = lean_ctor_get(v_r_3330_, 0);
v_k_3515_ = lean_ctor_get(v_r_3330_, 1);
v_v_3516_ = lean_ctor_get(v_r_3330_, 2);
v_l_3517_ = lean_ctor_get(v_r_3330_, 3);
lean_inc(v_l_3517_);
v_r_3518_ = lean_ctor_get(v_r_3330_, 4);
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_dec_lt(v_size_3509_, v_size_3514_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3656_; 
lean_inc(v_l_3512_);
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; lean_object* v_unused_3658_; lean_object* v_unused_3659_; lean_object* v_unused_3660_; lean_object* v_unused_3661_; 
v_unused_3657_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3657_);
v_unused_3658_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3659_);
v_unused_3660_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3660_);
v_unused_3661_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3661_);
v___x_3522_ = v_l_3329_;
v_isShared_3523_ = v_isSharedCheck_3656_;
goto v_resetjp_3521_;
}
else
{
lean_dec(v_l_3329_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3656_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v_tree_3525_; 
v___x_3524_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3510_, v_v_3511_, v_l_3512_, v_r_3513_);
v_tree_3525_ = lean_ctor_get(v___x_3524_, 2);
lean_inc(v_tree_3525_);
if (lean_obj_tag(v_tree_3525_) == 0)
{
lean_object* v_k_3526_; lean_object* v_v_3527_; lean_object* v_size_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_k_3526_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_k_3526_);
v_v_3527_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_v_3527_);
lean_dec_ref(v___x_3524_);
v_size_3528_ = lean_ctor_get(v_tree_3525_, 0);
v___x_3529_ = lean_unsigned_to_nat(3u);
v___x_3530_ = lean_nat_mul(v___x_3529_, v_size_3528_);
v___x_3531_ = lean_nat_dec_lt(v___x_3530_, v_size_3514_);
lean_dec(v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
lean_dec(v_l_3517_);
v___x_3532_ = lean_nat_add(v___x_3519_, v_size_3528_);
v___x_3533_ = lean_nat_add(v___x_3532_, v_size_3514_);
lean_dec(v___x_3532_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_r_3330_);
lean_ctor_set(v___x_3522_, 3, v_tree_3525_);
lean_ctor_set(v___x_3522_, 2, v_v_3527_);
lean_ctor_set(v___x_3522_, 1, v_k_3526_);
lean_ctor_set(v___x_3522_, 0, v___x_3533_);
v___x_3535_ = v___x_3522_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v_tree_3525_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_r_3330_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
else
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3591_; 
lean_inc(v_r_3518_);
lean_inc(v_v_3516_);
lean_inc(v_k_3515_);
lean_inc(v_size_3514_);
v_isSharedCheck_3591_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; lean_object* v_unused_3593_; lean_object* v_unused_3594_; lean_object* v_unused_3595_; lean_object* v_unused_3596_; 
v_unused_3592_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3592_);
v_unused_3593_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_r_3330_, 2);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_r_3330_, 1);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3596_);
v___x_3538_ = v_r_3330_;
v_isShared_3539_ = v_isSharedCheck_3591_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v_r_3330_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3591_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_size_3540_; lean_object* v_k_3541_; lean_object* v_v_3542_; lean_object* v_l_3543_; lean_object* v_r_3544_; lean_object* v_size_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_size_3540_ = lean_ctor_get(v_l_3517_, 0);
v_k_3541_ = lean_ctor_get(v_l_3517_, 1);
v_v_3542_ = lean_ctor_get(v_l_3517_, 2);
v_l_3543_ = lean_ctor_get(v_l_3517_, 3);
v_r_3544_ = lean_ctor_get(v_l_3517_, 4);
v_size_3545_ = lean_ctor_get(v_r_3518_, 0);
v___x_3546_ = lean_unsigned_to_nat(2u);
v___x_3547_ = lean_nat_mul(v___x_3546_, v_size_3545_);
v___x_3548_ = lean_nat_dec_lt(v_size_3540_, v___x_3547_);
lean_dec(v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3576_; 
lean_inc(v_r_3544_);
lean_inc(v_l_3543_);
lean_inc(v_v_3542_);
lean_inc(v_k_3541_);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_l_3517_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; 
v_unused_3577_ = lean_ctor_get(v_l_3517_, 4);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_l_3517_, 3);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_l_3517_, 2);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_l_3517_, 1);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_l_3517_, 0);
lean_dec(v_unused_3581_);
v___x_3550_ = v_l_3517_;
v_isShared_3551_ = v_isSharedCheck_3576_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v_l_3517_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3576_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3566_; 
v___x_3552_ = lean_nat_add(v___x_3519_, v_size_3528_);
v___x_3553_ = lean_nat_add(v___x_3552_, v_size_3514_);
lean_dec(v_size_3514_);
if (lean_obj_tag(v_l_3543_) == 0)
{
lean_object* v_size_3574_; 
v_size_3574_ = lean_ctor_get(v_l_3543_, 0);
lean_inc(v_size_3574_);
v___y_3566_ = v_size_3574_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_unsigned_to_nat(0u);
v___y_3566_ = v___x_3575_;
goto v___jp_3565_;
}
v___jp_3554_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_nat_add(v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec(v___y_3556_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 4, v_r_3518_);
lean_ctor_set(v___x_3550_, 3, v_r_3544_);
lean_ctor_set(v___x_3550_, 2, v_v_3516_);
lean_ctor_set(v___x_3550_, 1, v_k_3515_);
lean_ctor_set(v___x_3550_, 0, v___x_3558_);
v___x_3560_ = v___x_3550_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_r_3544_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_r_3518_);
v___x_3560_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 4, v___x_3560_);
lean_ctor_set(v___x_3538_, 3, v___y_3555_);
lean_ctor_set(v___x_3538_, 2, v_v_3542_);
lean_ctor_set(v___x_3538_, 1, v_k_3541_);
lean_ctor_set(v___x_3538_, 0, v___x_3553_);
v___x_3562_ = v___x_3538_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_k_3541_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_v_3542_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v___y_3555_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
v___jp_3565_:
{
lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3567_ = lean_nat_add(v___x_3552_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec(v___x_3552_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_l_3543_);
lean_ctor_set(v___x_3522_, 3, v_tree_3525_);
lean_ctor_set(v___x_3522_, 2, v_v_3527_);
lean_ctor_set(v___x_3522_, 1, v_k_3526_);
lean_ctor_set(v___x_3522_, 0, v___x_3567_);
v___x_3569_ = v___x_3522_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3573_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3573_, 3, v_tree_3525_);
lean_ctor_set(v_reuseFailAlloc_3573_, 4, v_l_3543_);
v___x_3569_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; 
v___x_3570_ = lean_nat_add(v___x_3519_, v_size_3545_);
if (lean_obj_tag(v_r_3544_) == 0)
{
lean_object* v_size_3571_; 
v_size_3571_ = lean_ctor_get(v_r_3544_, 0);
lean_inc(v_size_3571_);
v___y_3555_ = v___x_3569_;
v___y_3556_ = v___x_3570_;
v___y_3557_ = v_size_3571_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_unsigned_to_nat(0u);
v___y_3555_ = v___x_3569_;
v___y_3556_ = v___x_3570_;
v___y_3557_ = v___x_3572_;
goto v___jp_3554_;
}
}
}
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3582_ = lean_nat_add(v___x_3519_, v_size_3528_);
v___x_3583_ = lean_nat_add(v___x_3582_, v_size_3514_);
lean_dec(v_size_3514_);
v___x_3584_ = lean_nat_add(v___x_3582_, v_size_3540_);
lean_dec(v___x_3582_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 4, v_l_3517_);
lean_ctor_set(v___x_3538_, 3, v_tree_3525_);
lean_ctor_set(v___x_3538_, 2, v_v_3527_);
lean_ctor_set(v___x_3538_, 1, v_k_3526_);
lean_ctor_set(v___x_3538_, 0, v___x_3584_);
v___x_3586_ = v___x_3538_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3590_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3590_, 3, v_tree_3525_);
lean_ctor_set(v_reuseFailAlloc_3590_, 4, v_l_3517_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3588_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_r_3518_);
lean_ctor_set(v___x_3522_, 3, v___x_3586_);
lean_ctor_set(v___x_3522_, 2, v_v_3516_);
lean_ctor_set(v___x_3522_, 1, v_k_3515_);
lean_ctor_set(v___x_3522_, 0, v___x_3583_);
v___x_3588_ = v___x_3522_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_r_3518_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
else
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3650_; 
lean_inc(v_r_3518_);
lean_inc(v_v_3516_);
lean_inc(v_k_3515_);
lean_inc(v_size_3514_);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3650_ == 0)
{
lean_object* v_unused_3651_; lean_object* v_unused_3652_; lean_object* v_unused_3653_; lean_object* v_unused_3654_; lean_object* v_unused_3655_; 
v_unused_3651_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_r_3330_, 2);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_r_3330_, 1);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3655_);
v___x_3598_ = v_r_3330_;
v_isShared_3599_ = v_isSharedCheck_3650_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v_r_3330_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3650_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
if (lean_obj_tag(v_l_3517_) == 0)
{
if (lean_obj_tag(v_r_3518_) == 0)
{
lean_object* v_k_3600_; lean_object* v_v_3601_; lean_object* v_size_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v_k_3600_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_k_3600_);
v_v_3601_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_v_3601_);
lean_dec_ref(v___x_3524_);
v_size_3602_ = lean_ctor_get(v_l_3517_, 0);
v___x_3603_ = lean_nat_add(v___x_3519_, v_size_3514_);
lean_dec(v_size_3514_);
v___x_3604_ = lean_nat_add(v___x_3519_, v_size_3602_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 4, v_l_3517_);
lean_ctor_set(v___x_3598_, 3, v_tree_3525_);
lean_ctor_set(v___x_3598_, 2, v_v_3601_);
lean_ctor_set(v___x_3598_, 1, v_k_3600_);
lean_ctor_set(v___x_3598_, 0, v___x_3604_);
v___x_3606_ = v___x_3598_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3600_);
lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3601_);
lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_tree_3525_);
lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_l_3517_);
v___x_3606_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_r_3518_);
lean_ctor_set(v___x_3522_, 3, v___x_3606_);
lean_ctor_set(v___x_3522_, 2, v_v_3516_);
lean_ctor_set(v___x_3522_, 1, v_k_3515_);
lean_ctor_set(v___x_3522_, 0, v___x_3603_);
v___x_3608_ = v___x_3522_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_r_3518_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_k_3611_; lean_object* v_v_3612_; lean_object* v_k_3613_; lean_object* v_v_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_size_3514_);
v_k_3611_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_k_3611_);
v_v_3612_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_v_3612_);
lean_dec_ref(v___x_3524_);
v_k_3613_ = lean_ctor_get(v_l_3517_, 1);
v_v_3614_ = lean_ctor_get(v_l_3517_, 2);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_l_3517_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; 
v_unused_3629_ = lean_ctor_get(v_l_3517_, 4);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_l_3517_, 3);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_l_3517_, 0);
lean_dec(v_unused_3631_);
v___x_3616_ = v_l_3517_;
v_isShared_3617_ = v_isSharedCheck_3628_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_v_3614_);
lean_inc(v_k_3613_);
lean_dec(v_l_3517_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3628_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3618_ = lean_unsigned_to_nat(3u);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 4, v_r_3518_);
lean_ctor_set(v___x_3616_, 3, v_r_3518_);
lean_ctor_set(v___x_3616_, 2, v_v_3612_);
lean_ctor_set(v___x_3616_, 1, v_k_3611_);
lean_ctor_set(v___x_3616_, 0, v___x_3519_);
v___x_3620_ = v___x_3616_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_k_3611_);
lean_ctor_set(v_reuseFailAlloc_3627_, 2, v_v_3612_);
lean_ctor_set(v_reuseFailAlloc_3627_, 3, v_r_3518_);
lean_ctor_set(v_reuseFailAlloc_3627_, 4, v_r_3518_);
v___x_3620_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3622_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 3, v_r_3518_);
lean_ctor_set(v___x_3598_, 0, v___x_3519_);
v___x_3622_ = v___x_3598_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_r_3518_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_r_3518_);
v___x_3622_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3624_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v___x_3622_);
lean_ctor_set(v___x_3522_, 3, v___x_3620_);
lean_ctor_set(v___x_3522_, 2, v_v_3614_);
lean_ctor_set(v___x_3522_, 1, v_k_3613_);
lean_ctor_set(v___x_3522_, 0, v___x_3618_);
v___x_3624_ = v___x_3522_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3613_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3614_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v___x_3622_);
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
if (lean_obj_tag(v_r_3518_) == 0)
{
lean_object* v_k_3632_; lean_object* v_v_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_dec(v_size_3514_);
v_k_3632_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_k_3632_);
v_v_3633_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_v_3633_);
lean_dec_ref(v___x_3524_);
v___x_3634_ = lean_unsigned_to_nat(3u);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 4, v_l_3517_);
lean_ctor_set(v___x_3598_, 2, v_v_3633_);
lean_ctor_set(v___x_3598_, 1, v_k_3632_);
lean_ctor_set(v___x_3598_, 0, v___x_3519_);
v___x_3636_ = v___x_3598_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_k_3632_);
lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_v_3633_);
lean_ctor_set(v_reuseFailAlloc_3640_, 3, v_l_3517_);
lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_l_3517_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v_r_3518_);
lean_ctor_set(v___x_3522_, 3, v___x_3636_);
lean_ctor_set(v___x_3522_, 2, v_v_3516_);
lean_ctor_set(v___x_3522_, 1, v_k_3515_);
lean_ctor_set(v___x_3522_, 0, v___x_3634_);
v___x_3638_ = v___x_3522_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_r_3518_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
lean_object* v_k_3641_; lean_object* v_v_3642_; lean_object* v___x_3644_; 
v_k_3641_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_k_3641_);
v_v_3642_ = lean_ctor_get(v___x_3524_, 1);
lean_inc(v_v_3642_);
lean_dec_ref(v___x_3524_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 3, v_r_3518_);
v___x_3644_ = v___x_3598_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_size_3514_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v_k_3515_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v_v_3516_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_r_3518_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v_r_3518_);
v___x_3644_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = lean_unsigned_to_nat(2u);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 4, v___x_3644_);
lean_ctor_set(v___x_3522_, 3, v_r_3518_);
lean_ctor_set(v___x_3522_, 2, v_v_3642_);
lean_ctor_set(v___x_3522_, 1, v_k_3641_);
lean_ctor_set(v___x_3522_, 0, v___x_3645_);
v___x_3647_ = v___x_3522_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3641_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3642_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_r_3518_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v___x_3644_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
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
lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3814_; 
lean_inc(v_r_3518_);
lean_inc(v_v_3516_);
lean_inc(v_k_3515_);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_r_3330_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; 
v_unused_3815_ = lean_ctor_get(v_r_3330_, 4);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_r_3330_, 3);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3330_, 2);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_r_3330_, 1);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_r_3330_, 0);
lean_dec(v_unused_3819_);
v___x_3663_ = v_r_3330_;
v_isShared_3664_ = v_isSharedCheck_3814_;
goto v_resetjp_3662_;
}
else
{
lean_dec(v_r_3330_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3814_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; lean_object* v_tree_3666_; 
v___x_3665_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3515_, v_v_3516_, v_l_3517_, v_r_3518_);
v_tree_3666_ = lean_ctor_get(v___x_3665_, 2);
lean_inc(v_tree_3666_);
if (lean_obj_tag(v_tree_3666_) == 0)
{
lean_object* v_k_3667_; lean_object* v_v_3668_; lean_object* v_size_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; uint8_t v___x_3672_; 
v_k_3667_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_k_3667_);
v_v_3668_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_v_3668_);
lean_dec_ref(v___x_3665_);
v_size_3669_ = lean_ctor_get(v_tree_3666_, 0);
v___x_3670_ = lean_unsigned_to_nat(3u);
v___x_3671_ = lean_nat_mul(v___x_3670_, v_size_3669_);
v___x_3672_ = lean_nat_dec_lt(v___x_3671_, v_size_3509_);
lean_dec(v___x_3671_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_dec(v_r_3513_);
v___x_3673_ = lean_nat_add(v___x_3519_, v_size_3509_);
v___x_3674_ = lean_nat_add(v___x_3673_, v_size_3669_);
lean_dec(v___x_3673_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_tree_3666_);
lean_ctor_set(v___x_3663_, 3, v_l_3329_);
lean_ctor_set(v___x_3663_, 2, v_v_3668_);
lean_ctor_set(v___x_3663_, 1, v_k_3667_);
lean_ctor_set(v___x_3663_, 0, v___x_3674_);
v___x_3676_ = v___x_3663_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3677_, 4, v_tree_3666_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
else
{
lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3743_; 
lean_inc(v_l_3512_);
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
lean_inc(v_size_3509_);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; 
v_unused_3744_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3748_);
v___x_3679_ = v_l_3329_;
v_isShared_3680_ = v_isSharedCheck_3743_;
goto v_resetjp_3678_;
}
else
{
lean_dec(v_l_3329_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3743_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v_size_3681_; lean_object* v_size_3682_; lean_object* v_k_3683_; lean_object* v_v_3684_; lean_object* v_l_3685_; lean_object* v_r_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; uint8_t v___x_3689_; 
v_size_3681_ = lean_ctor_get(v_l_3512_, 0);
v_size_3682_ = lean_ctor_get(v_r_3513_, 0);
v_k_3683_ = lean_ctor_get(v_r_3513_, 1);
v_v_3684_ = lean_ctor_get(v_r_3513_, 2);
v_l_3685_ = lean_ctor_get(v_r_3513_, 3);
v_r_3686_ = lean_ctor_get(v_r_3513_, 4);
v___x_3687_ = lean_unsigned_to_nat(2u);
v___x_3688_ = lean_nat_mul(v___x_3687_, v_size_3681_);
v___x_3689_ = lean_nat_dec_lt(v_size_3682_, v___x_3688_);
lean_dec(v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3727_; 
lean_inc(v_r_3686_);
lean_inc(v_l_3685_);
lean_inc(v_v_3684_);
lean_inc(v_k_3683_);
lean_del_object(v___x_3679_);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_r_3513_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; 
v_unused_3728_ = lean_ctor_get(v_r_3513_, 4);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_r_3513_, 3);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_r_3513_, 2);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_r_3513_, 1);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3513_, 0);
lean_dec(v_unused_3732_);
v___x_3691_ = v_r_3513_;
v_isShared_3692_ = v_isSharedCheck_3727_;
goto v_resetjp_3690_;
}
else
{
lean_dec(v_r_3513_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3727_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___x_3715_; lean_object* v___y_3717_; 
v___x_3693_ = lean_nat_add(v___x_3519_, v_size_3509_);
lean_dec(v_size_3509_);
v___x_3694_ = lean_nat_add(v___x_3693_, v_size_3669_);
lean_dec(v___x_3693_);
v___x_3715_ = lean_nat_add(v___x_3519_, v_size_3681_);
if (lean_obj_tag(v_l_3685_) == 0)
{
lean_object* v_size_3725_; 
v_size_3725_ = lean_ctor_get(v_l_3685_, 0);
lean_inc(v_size_3725_);
v___y_3717_ = v_size_3725_;
goto v___jp_3716_;
}
else
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___y_3717_ = v___x_3726_;
goto v___jp_3716_;
}
v___jp_3695_:
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
v___x_3699_ = lean_nat_add(v___y_3696_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec(v___y_3696_);
lean_inc_ref(v_tree_3666_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 4, v_tree_3666_);
lean_ctor_set(v___x_3691_, 3, v_r_3686_);
lean_ctor_set(v___x_3691_, 2, v_v_3668_);
lean_ctor_set(v___x_3691_, 1, v_k_3667_);
lean_ctor_set(v___x_3691_, 0, v___x_3699_);
v___x_3701_ = v___x_3691_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_r_3686_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v_tree_3666_);
v___x_3701_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_tree_3666_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; 
v_unused_3709_ = lean_ctor_get(v_tree_3666_, 4);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_tree_3666_, 3);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_tree_3666_, 2);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_tree_3666_, 1);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_tree_3666_, 0);
lean_dec(v_unused_3713_);
v___x_3703_ = v_tree_3666_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_dec(v_tree_3666_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 4, v___x_3701_);
lean_ctor_set(v___x_3703_, 3, v___y_3697_);
lean_ctor_set(v___x_3703_, 2, v_v_3684_);
lean_ctor_set(v___x_3703_, 1, v_k_3683_);
lean_ctor_set(v___x_3703_, 0, v___x_3694_);
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3683_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3684_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v___y_3697_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v___x_3701_);
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
v___jp_3716_:
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3718_ = lean_nat_add(v___x_3715_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec(v___x_3715_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_l_3685_);
lean_ctor_set(v___x_3663_, 3, v_l_3512_);
lean_ctor_set(v___x_3663_, 2, v_v_3511_);
lean_ctor_set(v___x_3663_, 1, v_k_3510_);
lean_ctor_set(v___x_3663_, 0, v___x_3718_);
v___x_3720_ = v___x_3663_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3724_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3724_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3724_, 4, v_l_3685_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_nat_add(v___x_3519_, v_size_3669_);
if (lean_obj_tag(v_r_3686_) == 0)
{
lean_object* v_size_3722_; 
v_size_3722_ = lean_ctor_get(v_r_3686_, 0);
lean_inc(v_size_3722_);
v___y_3696_ = v___x_3721_;
v___y_3697_ = v___x_3720_;
v___y_3698_ = v_size_3722_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_unsigned_to_nat(0u);
v___y_3696_ = v___x_3721_;
v___y_3697_ = v___x_3720_;
v___y_3698_ = v___x_3723_;
goto v___jp_3695_;
}
}
}
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v___x_3733_ = lean_nat_add(v___x_3519_, v_size_3509_);
lean_dec(v_size_3509_);
v___x_3734_ = lean_nat_add(v___x_3733_, v_size_3669_);
lean_dec(v___x_3733_);
v___x_3735_ = lean_nat_add(v___x_3519_, v_size_3669_);
v___x_3736_ = lean_nat_add(v___x_3735_, v_size_3682_);
lean_dec(v___x_3735_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_tree_3666_);
lean_ctor_set(v___x_3663_, 3, v_r_3513_);
lean_ctor_set(v___x_3663_, 2, v_v_3668_);
lean_ctor_set(v___x_3663_, 1, v_k_3667_);
lean_ctor_set(v___x_3663_, 0, v___x_3736_);
v___x_3738_ = v___x_3663_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_r_3513_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_tree_3666_);
v___x_3738_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
lean_object* v___x_3740_; 
if (v_isShared_3680_ == 0)
{
lean_ctor_set(v___x_3679_, 4, v___x_3738_);
lean_ctor_set(v___x_3679_, 0, v___x_3734_);
v___x_3740_ = v___x_3679_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3512_) == 0)
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3772_; 
lean_inc_ref(v_l_3512_);
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
lean_inc(v_size_3509_);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; lean_object* v_unused_3774_; lean_object* v_unused_3775_; lean_object* v_unused_3776_; lean_object* v_unused_3777_; 
v_unused_3773_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3777_);
v___x_3750_ = v_l_3329_;
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v_l_3329_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3772_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
if (lean_obj_tag(v_r_3513_) == 0)
{
lean_object* v_k_3752_; lean_object* v_v_3753_; lean_object* v_size_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
v_k_3752_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_k_3752_);
v_v_3753_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_v_3753_);
lean_dec_ref(v___x_3665_);
v_size_3754_ = lean_ctor_get(v_r_3513_, 0);
v___x_3755_ = lean_nat_add(v___x_3519_, v_size_3509_);
lean_dec(v_size_3509_);
v___x_3756_ = lean_nat_add(v___x_3519_, v_size_3754_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_tree_3666_);
lean_ctor_set(v___x_3663_, 3, v_r_3513_);
lean_ctor_set(v___x_3663_, 2, v_v_3753_);
lean_ctor_set(v___x_3663_, 1, v_k_3752_);
lean_ctor_set(v___x_3663_, 0, v___x_3756_);
v___x_3758_ = v___x_3663_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3753_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_r_3513_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_tree_3666_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 4, v___x_3758_);
lean_ctor_set(v___x_3750_, 0, v___x_3755_);
v___x_3760_ = v___x_3750_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
else
{
lean_object* v_k_3763_; lean_object* v_v_3764_; lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec(v_size_3509_);
v_k_3763_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_k_3763_);
v_v_3764_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_v_3764_);
lean_dec_ref(v___x_3665_);
v___x_3765_ = lean_unsigned_to_nat(3u);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_r_3513_);
lean_ctor_set(v___x_3663_, 3, v_r_3513_);
lean_ctor_set(v___x_3663_, 2, v_v_3764_);
lean_ctor_set(v___x_3663_, 1, v_k_3763_);
lean_ctor_set(v___x_3663_, 0, v___x_3519_);
v___x_3767_ = v___x_3663_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3763_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3764_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_r_3513_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_r_3513_);
v___x_3767_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3769_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 4, v___x_3767_);
lean_ctor_set(v___x_3750_, 0, v___x_3765_);
v___x_3769_ = v___x_3750_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3513_) == 0)
{
lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3802_; 
lean_inc(v_l_3512_);
lean_inc(v_v_3511_);
lean_inc(v_k_3510_);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3802_ == 0)
{
lean_object* v_unused_3803_; lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; 
v_unused_3803_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3807_);
v___x_3779_ = v_l_3329_;
v_isShared_3780_ = v_isSharedCheck_3802_;
goto v_resetjp_3778_;
}
else
{
lean_dec(v_l_3329_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3802_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_k_3781_; lean_object* v_v_3782_; lean_object* v_k_3783_; lean_object* v_v_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3798_; 
v_k_3781_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_k_3781_);
v_v_3782_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_v_3782_);
lean_dec_ref(v___x_3665_);
v_k_3783_ = lean_ctor_get(v_r_3513_, 1);
v_v_3784_ = lean_ctor_get(v_r_3513_, 2);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_r_3513_);
if (v_isSharedCheck_3798_ == 0)
{
lean_object* v_unused_3799_; lean_object* v_unused_3800_; lean_object* v_unused_3801_; 
v_unused_3799_ = lean_ctor_get(v_r_3513_, 4);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_r_3513_, 3);
lean_dec(v_unused_3800_);
v_unused_3801_ = lean_ctor_get(v_r_3513_, 0);
lean_dec(v_unused_3801_);
v___x_3786_ = v_r_3513_;
v_isShared_3787_ = v_isSharedCheck_3798_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_v_3784_);
lean_inc(v_k_3783_);
lean_dec(v_r_3513_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3798_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3788_ = lean_unsigned_to_nat(3u);
if (v_isShared_3787_ == 0)
{
lean_ctor_set(v___x_3786_, 4, v_l_3512_);
lean_ctor_set(v___x_3786_, 3, v_l_3512_);
lean_ctor_set(v___x_3786_, 2, v_v_3511_);
lean_ctor_set(v___x_3786_, 1, v_k_3510_);
lean_ctor_set(v___x_3786_, 0, v___x_3519_);
v___x_3790_ = v___x_3786_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3510_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3511_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v_l_3512_);
v___x_3790_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
lean_object* v___x_3792_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_l_3512_);
lean_ctor_set(v___x_3663_, 3, v_l_3512_);
lean_ctor_set(v___x_3663_, 2, v_v_3782_);
lean_ctor_set(v___x_3663_, 1, v_k_3781_);
lean_ctor_set(v___x_3663_, 0, v___x_3519_);
v___x_3792_ = v___x_3663_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3781_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3782_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_l_3512_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_l_3512_);
v___x_3792_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v___x_3792_);
lean_ctor_set(v___x_3779_, 3, v___x_3790_);
lean_ctor_set(v___x_3779_, 2, v_v_3784_);
lean_ctor_set(v___x_3779_, 1, v_k_3783_);
lean_ctor_set(v___x_3779_, 0, v___x_3788_);
v___x_3794_ = v___x_3779_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3788_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3783_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3784_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v___x_3792_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
}
}
else
{
lean_object* v_k_3808_; lean_object* v_v_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v_k_3808_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_k_3808_);
v_v_3809_ = lean_ctor_get(v___x_3665_, 1);
lean_inc(v_v_3809_);
lean_dec_ref(v___x_3665_);
v___x_3810_ = lean_unsigned_to_nat(2u);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_r_3513_);
lean_ctor_set(v___x_3663_, 3, v_l_3329_);
lean_ctor_set(v___x_3663_, 2, v_v_3809_);
lean_ctor_set(v___x_3663_, 1, v_k_3808_);
lean_ctor_set(v___x_3663_, 0, v___x_3810_);
v___x_3812_ = v___x_3663_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3513_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
}
else
{
return v_l_3329_;
}
}
else
{
return v_r_3330_;
}
}
default: 
{
lean_object* v_impl_3820_; lean_object* v___x_3821_; 
v_impl_3820_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3325_, v_r_3330_);
v___x_3821_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3820_) == 0)
{
if (lean_obj_tag(v_l_3329_) == 0)
{
lean_object* v_size_3822_; lean_object* v_size_3823_; lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v_l_3826_; lean_object* v_r_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_size_3822_ = lean_ctor_get(v_impl_3820_, 0);
lean_inc(v_size_3822_);
v_size_3823_ = lean_ctor_get(v_l_3329_, 0);
v_k_3824_ = lean_ctor_get(v_l_3329_, 1);
v_v_3825_ = lean_ctor_get(v_l_3329_, 2);
v_l_3826_ = lean_ctor_get(v_l_3329_, 3);
v_r_3827_ = lean_ctor_get(v_l_3329_, 4);
lean_inc(v_r_3827_);
v___x_3828_ = lean_unsigned_to_nat(3u);
v___x_3829_ = lean_nat_mul(v___x_3828_, v_size_3822_);
v___x_3830_ = lean_nat_dec_lt(v___x_3829_, v_size_3823_);
lean_dec(v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_r_3827_);
v___x_3831_ = lean_nat_add(v___x_3821_, v_size_3823_);
v___x_3832_ = lean_nat_add(v___x_3831_, v_size_3822_);
lean_dec(v_size_3822_);
lean_dec(v___x_3831_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_impl_3820_);
lean_ctor_set(v___x_3332_, 0, v___x_3832_);
v___x_3834_ = v___x_3332_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_impl_3820_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3901_; 
lean_inc(v_l_3826_);
lean_inc(v_v_3825_);
lean_inc(v_k_3824_);
lean_inc(v_size_3823_);
v_isSharedCheck_3901_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; lean_object* v_unused_3906_; 
v_unused_3902_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_l_3329_, 2);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_l_3329_, 1);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3906_);
v___x_3837_ = v_l_3329_;
v_isShared_3838_ = v_isSharedCheck_3901_;
goto v_resetjp_3836_;
}
else
{
lean_dec(v_l_3329_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3901_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_size_3839_; lean_object* v_size_3840_; lean_object* v_k_3841_; lean_object* v_v_3842_; lean_object* v_l_3843_; lean_object* v_r_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_size_3839_ = lean_ctor_get(v_l_3826_, 0);
v_size_3840_ = lean_ctor_get(v_r_3827_, 0);
v_k_3841_ = lean_ctor_get(v_r_3827_, 1);
v_v_3842_ = lean_ctor_get(v_r_3827_, 2);
v_l_3843_ = lean_ctor_get(v_r_3827_, 3);
v_r_3844_ = lean_ctor_get(v_r_3827_, 4);
v___x_3845_ = lean_unsigned_to_nat(2u);
v___x_3846_ = lean_nat_mul(v___x_3845_, v_size_3839_);
v___x_3847_ = lean_nat_dec_lt(v_size_3840_, v___x_3846_);
lean_dec(v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3876_; 
lean_inc(v_r_3844_);
lean_inc(v_l_3843_);
lean_inc(v_v_3842_);
lean_inc(v_k_3841_);
v_isSharedCheck_3876_ = !lean_is_exclusive(v_r_3827_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; 
v_unused_3877_ = lean_ctor_get(v_r_3827_, 4);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_r_3827_, 3);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_r_3827_, 2);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_r_3827_, 1);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_r_3827_, 0);
lean_dec(v_unused_3881_);
v___x_3849_ = v_r_3827_;
v_isShared_3850_ = v_isSharedCheck_3876_;
goto v_resetjp_3848_;
}
else
{
lean_dec(v_r_3827_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3876_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___x_3864_; lean_object* v___y_3866_; 
v___x_3851_ = lean_nat_add(v___x_3821_, v_size_3823_);
lean_dec(v_size_3823_);
v___x_3852_ = lean_nat_add(v___x_3851_, v_size_3822_);
lean_dec(v___x_3851_);
v___x_3864_ = lean_nat_add(v___x_3821_, v_size_3839_);
if (lean_obj_tag(v_l_3843_) == 0)
{
lean_object* v_size_3874_; 
v_size_3874_ = lean_ctor_get(v_l_3843_, 0);
lean_inc(v_size_3874_);
v___y_3866_ = v_size_3874_;
goto v___jp_3865_;
}
else
{
lean_object* v___x_3875_; 
v___x_3875_ = lean_unsigned_to_nat(0u);
v___y_3866_ = v___x_3875_;
goto v___jp_3865_;
}
v___jp_3853_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = lean_nat_add(v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 4, v_impl_3820_);
lean_ctor_set(v___x_3849_, 3, v_r_3844_);
lean_ctor_set(v___x_3849_, 2, v_v_3328_);
lean_ctor_set(v___x_3849_, 1, v_k_3327_);
lean_ctor_set(v___x_3849_, 0, v___x_3857_);
v___x_3859_ = v___x_3849_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_r_3844_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_impl_3820_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v___x_3859_);
lean_ctor_set(v___x_3837_, 3, v___y_3854_);
lean_ctor_set(v___x_3837_, 2, v_v_3842_);
lean_ctor_set(v___x_3837_, 1, v_k_3841_);
lean_ctor_set(v___x_3837_, 0, v___x_3852_);
v___x_3861_ = v___x_3837_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3841_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3842_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v___y_3854_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
v___jp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = lean_nat_add(v___x_3864_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec(v___x_3864_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3843_);
lean_ctor_set(v___x_3332_, 3, v_l_3826_);
lean_ctor_set(v___x_3332_, 2, v_v_3825_);
lean_ctor_set(v___x_3332_, 1, v_k_3824_);
lean_ctor_set(v___x_3332_, 0, v___x_3867_);
v___x_3869_ = v___x_3332_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v_l_3826_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v_l_3843_);
v___x_3869_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_nat_add(v___x_3821_, v_size_3822_);
lean_dec(v_size_3822_);
if (lean_obj_tag(v_r_3844_) == 0)
{
lean_object* v_size_3871_; 
v_size_3871_ = lean_ctor_get(v_r_3844_, 0);
lean_inc(v_size_3871_);
v___y_3854_ = v___x_3869_;
v___y_3855_ = v___x_3870_;
v___y_3856_ = v_size_3871_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
v___y_3854_ = v___x_3869_;
v___y_3855_ = v___x_3870_;
v___y_3856_ = v___x_3872_;
goto v___jp_3853_;
}
}
}
}
}
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_del_object(v___x_3332_);
v___x_3882_ = lean_nat_add(v___x_3821_, v_size_3823_);
lean_dec(v_size_3823_);
v___x_3883_ = lean_nat_add(v___x_3882_, v_size_3822_);
lean_dec(v___x_3882_);
v___x_3884_ = lean_nat_add(v___x_3821_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3885_ = lean_nat_add(v___x_3884_, v_size_3840_);
lean_dec(v___x_3884_);
lean_inc_ref(v_impl_3820_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v_impl_3820_);
lean_ctor_set(v___x_3837_, 3, v_r_3827_);
lean_ctor_set(v___x_3837_, 2, v_v_3328_);
lean_ctor_set(v___x_3837_, 1, v_k_3327_);
lean_ctor_set(v___x_3837_, 0, v___x_3885_);
v___x_3887_ = v___x_3837_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3900_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3900_, 3, v_r_3827_);
lean_ctor_set(v_reuseFailAlloc_3900_, 4, v_impl_3820_);
v___x_3887_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v_impl_3820_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3895_ = lean_ctor_get(v_impl_3820_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3820_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3820_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3820_, 1);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_impl_3820_, 0);
lean_dec(v_unused_3899_);
v___x_3889_ = v_impl_3820_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v_impl_3820_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 4, v___x_3887_);
lean_ctor_set(v___x_3889_, 3, v_l_3826_);
lean_ctor_set(v___x_3889_, 2, v_v_3825_);
lean_ctor_set(v___x_3889_, 1, v_k_3824_);
lean_ctor_set(v___x_3889_, 0, v___x_3883_);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_l_3826_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v___x_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
v_size_3907_ = lean_ctor_get(v_impl_3820_, 0);
lean_inc(v_size_3907_);
v___x_3908_ = lean_nat_add(v___x_3821_, v_size_3907_);
lean_dec(v_size_3907_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_impl_3820_);
lean_ctor_set(v___x_3332_, 0, v___x_3908_);
v___x_3910_ = v___x_3332_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_impl_3820_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
else
{
if (lean_obj_tag(v_l_3329_) == 0)
{
lean_object* v_l_3912_; 
v_l_3912_ = lean_ctor_get(v_l_3329_, 3);
if (lean_obj_tag(v_l_3912_) == 0)
{
lean_object* v_r_3913_; 
lean_inc_ref(v_l_3912_);
v_r_3913_ = lean_ctor_get(v_l_3329_, 4);
lean_inc(v_r_3913_);
if (lean_obj_tag(v_r_3913_) == 0)
{
lean_object* v_size_3914_; lean_object* v_k_3915_; lean_object* v_v_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3929_; 
v_size_3914_ = lean_ctor_get(v_l_3329_, 0);
v_k_3915_ = lean_ctor_get(v_l_3329_, 1);
v_v_3916_ = lean_ctor_get(v_l_3329_, 2);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; lean_object* v_unused_3931_; 
v_unused_3930_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3931_);
v___x_3918_ = v_l_3329_;
v_isShared_3919_ = v_isSharedCheck_3929_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_v_3916_);
lean_inc(v_k_3915_);
lean_inc(v_size_3914_);
lean_dec(v_l_3329_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3929_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v_size_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3924_; 
v_size_3920_ = lean_ctor_get(v_r_3913_, 0);
v___x_3921_ = lean_nat_add(v___x_3821_, v_size_3914_);
lean_dec(v_size_3914_);
v___x_3922_ = lean_nat_add(v___x_3821_, v_size_3920_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 4, v_impl_3820_);
lean_ctor_set(v___x_3918_, 3, v_r_3913_);
lean_ctor_set(v___x_3918_, 2, v_v_3328_);
lean_ctor_set(v___x_3918_, 1, v_k_3327_);
lean_ctor_set(v___x_3918_, 0, v___x_3922_);
v___x_3924_ = v___x_3918_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3928_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3928_, 3, v_r_3913_);
lean_ctor_set(v_reuseFailAlloc_3928_, 4, v_impl_3820_);
v___x_3924_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3926_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3924_);
lean_ctor_set(v___x_3332_, 3, v_l_3912_);
lean_ctor_set(v___x_3332_, 2, v_v_3916_);
lean_ctor_set(v___x_3332_, 1, v_k_3915_);
lean_ctor_set(v___x_3332_, 0, v___x_3921_);
v___x_3926_ = v___x_3332_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3915_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3916_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_l_3912_);
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
else
{
lean_object* v_k_3932_; lean_object* v_v_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3944_; 
v_k_3932_ = lean_ctor_get(v_l_3329_, 1);
v_v_3933_ = lean_ctor_get(v_l_3329_, 2);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; lean_object* v_unused_3946_; lean_object* v_unused_3947_; 
v_unused_3945_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3947_);
v___x_3935_ = v_l_3329_;
v_isShared_3936_ = v_isSharedCheck_3944_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_v_3933_);
lean_inc(v_k_3932_);
lean_dec(v_l_3329_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3944_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_unsigned_to_nat(3u);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 3, v_r_3913_);
lean_ctor_set(v___x_3935_, 2, v_v_3328_);
lean_ctor_set(v___x_3935_, 1, v_k_3327_);
lean_ctor_set(v___x_3935_, 0, v___x_3821_);
v___x_3939_ = v___x_3935_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3943_, 3, v_r_3913_);
lean_ctor_set(v_reuseFailAlloc_3943_, 4, v_r_3913_);
v___x_3939_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
lean_object* v___x_3941_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3939_);
lean_ctor_set(v___x_3332_, 3, v_l_3912_);
lean_ctor_set(v___x_3332_, 2, v_v_3933_);
lean_ctor_set(v___x_3332_, 1, v_k_3932_);
lean_ctor_set(v___x_3332_, 0, v___x_3937_);
v___x_3941_ = v___x_3332_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_k_3932_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_v_3933_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_l_3912_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v___x_3939_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
else
{
lean_object* v_r_3948_; 
v_r_3948_ = lean_ctor_get(v_l_3329_, 4);
lean_inc(v_r_3948_);
if (lean_obj_tag(v_r_3948_) == 0)
{
lean_object* v_k_3949_; lean_object* v_v_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3973_; 
lean_inc(v_l_3912_);
v_k_3949_ = lean_ctor_get(v_l_3329_, 1);
v_v_3950_ = lean_ctor_get(v_l_3329_, 2);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_l_3329_);
if (v_isSharedCheck_3973_ == 0)
{
lean_object* v_unused_3974_; lean_object* v_unused_3975_; lean_object* v_unused_3976_; 
v_unused_3974_ = lean_ctor_get(v_l_3329_, 4);
lean_dec(v_unused_3974_);
v_unused_3975_ = lean_ctor_get(v_l_3329_, 3);
lean_dec(v_unused_3975_);
v_unused_3976_ = lean_ctor_get(v_l_3329_, 0);
lean_dec(v_unused_3976_);
v___x_3952_ = v_l_3329_;
v_isShared_3953_ = v_isSharedCheck_3973_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_v_3950_);
lean_inc(v_k_3949_);
lean_dec(v_l_3329_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3973_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v_k_3954_; lean_object* v_v_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3969_; 
v_k_3954_ = lean_ctor_get(v_r_3948_, 1);
v_v_3955_ = lean_ctor_get(v_r_3948_, 2);
v_isSharedCheck_3969_ = !lean_is_exclusive(v_r_3948_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; lean_object* v_unused_3971_; lean_object* v_unused_3972_; 
v_unused_3970_ = lean_ctor_get(v_r_3948_, 4);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_r_3948_, 3);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_r_3948_, 0);
lean_dec(v_unused_3972_);
v___x_3957_ = v_r_3948_;
v_isShared_3958_ = v_isSharedCheck_3969_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_v_3955_);
lean_inc(v_k_3954_);
lean_dec(v_r_3948_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3969_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3959_ = lean_unsigned_to_nat(3u);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 4, v_l_3912_);
lean_ctor_set(v___x_3957_, 3, v_l_3912_);
lean_ctor_set(v___x_3957_, 2, v_v_3950_);
lean_ctor_set(v___x_3957_, 1, v_k_3949_);
lean_ctor_set(v___x_3957_, 0, v___x_3821_);
v___x_3961_ = v___x_3957_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_k_3949_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_v_3950_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_l_3912_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_l_3912_);
v___x_3961_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3963_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 4, v_l_3912_);
lean_ctor_set(v___x_3952_, 2, v_v_3328_);
lean_ctor_set(v___x_3952_, 1, v_k_3327_);
lean_ctor_set(v___x_3952_, 0, v___x_3821_);
v___x_3963_ = v___x_3952_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_l_3912_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_l_3912_);
v___x_3963_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v___x_3963_);
lean_ctor_set(v___x_3332_, 3, v___x_3961_);
lean_ctor_set(v___x_3332_, 2, v_v_3955_);
lean_ctor_set(v___x_3332_, 1, v_k_3954_);
lean_ctor_set(v___x_3332_, 0, v___x_3959_);
v___x_3965_ = v___x_3332_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_k_3954_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_v_3955_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3966_, 4, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
}
}
else
{
lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3977_ = lean_unsigned_to_nat(2u);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3948_);
lean_ctor_set(v___x_3332_, 0, v___x_3977_);
v___x_3979_ = v___x_3332_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_r_3948_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v___x_3982_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_l_3329_);
lean_ctor_set(v___x_3332_, 0, v___x_3821_);
v___x_3982_ = v___x_3332_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_l_3329_);
lean_ctor_set(v_reuseFailAlloc_3983_, 4, v_l_3329_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
}
}
else
{
return v_t_3326_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3986_, lean_object* v_t_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3986_, v_t_3987_);
lean_dec(v_k_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3989_, lean_object* v_x_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3989_, v_x_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3992_, lean_object* v_x_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3992_, v_x_3993_);
lean_dec(v_declName_3992_);
return v_res_3994_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3997_ = l_Lean_stringToMessageData(v___x_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; lean_object* v_env_4007_; lean_object* v___f_4008_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___x_4052_; 
v___x_4006_ = lean_st_ref_get(v___y_4004_);
v_env_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc_ref(v_env_4007_);
lean_dec(v___x_4006_);
lean_inc(v_declName_3998_);
v___f_4008_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4008_, 0, v_declName_3998_);
v___x_4052_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4007_, v_declName_3998_);
lean_dec_ref(v_env_4007_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_dec(v_declName_3998_);
v___y_4010_ = v___y_4002_;
v___y_4011_ = v___y_4004_;
goto v___jp_4009_;
}
else
{
uint8_t v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec_ref_known(v___x_4052_, 1);
lean_dec_ref(v___f_4008_);
v___x_4053_ = 0;
v___x_4054_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4055_ = l_Lean_MessageData_ofConstName(v_declName_3998_, v___x_4053_);
v___x_4056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4054_);
lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4056_);
lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4058_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4059_;
}
v___jp_4009_:
{
lean_object* v___x_4012_; lean_object* v_env_4013_; lean_object* v_nextMacroScope_4014_; lean_object* v_ngen_4015_; lean_object* v_auxDeclNGen_4016_; lean_object* v_traceState_4017_; lean_object* v_messages_4018_; lean_object* v_infoState_4019_; lean_object* v_snapshotTasks_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4050_; 
v___x_4012_ = lean_st_ref_take(v___y_4011_);
v_env_4013_ = lean_ctor_get(v___x_4012_, 0);
v_nextMacroScope_4014_ = lean_ctor_get(v___x_4012_, 1);
v_ngen_4015_ = lean_ctor_get(v___x_4012_, 2);
v_auxDeclNGen_4016_ = lean_ctor_get(v___x_4012_, 3);
v_traceState_4017_ = lean_ctor_get(v___x_4012_, 4);
v_messages_4018_ = lean_ctor_get(v___x_4012_, 6);
v_infoState_4019_ = lean_ctor_get(v___x_4012_, 7);
v_snapshotTasks_4020_ = lean_ctor_get(v___x_4012_, 8);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4050_ == 0)
{
lean_object* v_unused_4051_; 
v_unused_4051_ = lean_ctor_get(v___x_4012_, 5);
lean_dec(v_unused_4051_);
v___x_4022_ = v___x_4012_;
v_isShared_4023_ = v_isSharedCheck_4050_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_snapshotTasks_4020_);
lean_inc(v_infoState_4019_);
lean_inc(v_messages_4018_);
lean_inc(v_traceState_4017_);
lean_inc(v_auxDeclNGen_4016_);
lean_inc(v_ngen_4015_);
lean_inc(v_nextMacroScope_4014_);
lean_inc(v_env_4013_);
lean_dec(v___x_4012_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4050_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4024_ = l_Lean_docStringExt;
v___x_4025_ = lean_box(2);
v___x_4026_ = lean_box(0);
v___x_4027_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4024_, v_env_4013_, v___f_4008_, v___x_4025_, v___x_4026_);
v___x_4028_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 5, v___x_4028_);
lean_ctor_set(v___x_4022_, 0, v___x_4027_);
v___x_4030_ = v___x_4022_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_nextMacroScope_4014_);
lean_ctor_set(v_reuseFailAlloc_4049_, 2, v_ngen_4015_);
lean_ctor_set(v_reuseFailAlloc_4049_, 3, v_auxDeclNGen_4016_);
lean_ctor_set(v_reuseFailAlloc_4049_, 4, v_traceState_4017_);
lean_ctor_set(v_reuseFailAlloc_4049_, 5, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4049_, 6, v_messages_4018_);
lean_ctor_set(v_reuseFailAlloc_4049_, 7, v_infoState_4019_);
lean_ctor_set(v_reuseFailAlloc_4049_, 8, v_snapshotTasks_4020_);
v___x_4030_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v_mctx_4033_; lean_object* v_zetaDeltaFVarIds_4034_; lean_object* v_postponed_4035_; lean_object* v_diag_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4047_; 
v___x_4031_ = lean_st_ref_put(v___y_4011_, v___x_4030_);
v___x_4032_ = lean_st_ref_take(v___y_4010_);
v_mctx_4033_ = lean_ctor_get(v___x_4032_, 0);
v_zetaDeltaFVarIds_4034_ = lean_ctor_get(v___x_4032_, 2);
v_postponed_4035_ = lean_ctor_get(v___x_4032_, 3);
v_diag_4036_ = lean_ctor_get(v___x_4032_, 4);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; 
v_unused_4048_ = lean_ctor_get(v___x_4032_, 1);
lean_dec(v_unused_4048_);
v___x_4038_ = v___x_4032_;
v_isShared_4039_ = v_isSharedCheck_4047_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_diag_4036_);
lean_inc(v_postponed_4035_);
lean_inc(v_zetaDeltaFVarIds_4034_);
lean_inc(v_mctx_4033_);
lean_dec(v___x_4032_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4047_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
v___x_4040_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 1, v___x_4040_);
v___x_4042_ = v___x_4038_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_mctx_4033_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v___x_4040_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v_zetaDeltaFVarIds_4034_);
lean_ctor_set(v_reuseFailAlloc_4046_, 3, v_postponed_4035_);
lean_ctor_set(v_reuseFailAlloc_4046_, 4, v_diag_4036_);
v___x_4042_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4043_ = lean_st_ref_put(v___y_4010_, v___x_4042_);
v___x_4044_ = lean_box(0);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec_ref(v___y_4061_);
return v_res_4068_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4074_ = l_Lean_stringToMessageData(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4077_ = l_Lean_stringToMessageData(v___x_4076_);
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4080_ = l_Lean_stringToMessageData(v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v___x_4089_; lean_object* v_env_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; 
v___x_4089_ = lean_st_ref_get(v_a_4087_);
v_env_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = 1;
lean_inc(v_declName_4081_);
v___x_4092_ = l_Lean_findInternalDocString_x3f(v_env_4090_, v_declName_4081_, v___x_4091_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
if (lean_obj_tag(v_a_4093_) == 1)
{
lean_object* v_val_4094_; 
v_val_4094_ = lean_ctor_get(v_a_4093_, 0);
lean_inc(v_val_4094_);
lean_dec_ref_known(v_a_4093_, 1);
if (lean_obj_tag(v_val_4094_) == 0)
{
lean_object* v_val_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4117_; 
v_val_4095_ = lean_ctor_get(v_val_4094_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v_val_4094_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4097_ = v_val_4094_;
v_isShared_4098_ = v_isSharedCheck_4117_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_val_4095_);
lean_dec(v_val_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4117_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_removeBuiltinDocString(v_declName_4081_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v___x_4100_; 
lean_dec_ref_known(v___x_4099_, 1);
lean_del_object(v___x_4097_);
lean_inc(v_declName_4081_);
v___x_4100_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref_known(v___x_4100_, 1);
v___x_4101_ = l_Lean_addVersoDocStringFromString(v_declName_4081_, v_val_4095_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
return v___x_4101_;
}
else
{
lean_dec(v_val_4095_);
lean_dec(v_declName_4081_);
return v___x_4100_;
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v_val_4095_);
lean_dec(v_declName_4081_);
v_a_4102_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4104_ = v___x_4099_;
v_isShared_4105_ = v_isSharedCheck_4116_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4099_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4116_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v_ref_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v_ref_4106_ = lean_ctor_get(v_a_4086_, 5);
v___x_4107_ = lean_io_error_to_string(v_a_4102_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set_tag(v___x_4097_, 3);
lean_ctor_set(v___x_4097_, 0, v___x_4107_);
v___x_4109_ = v___x_4097_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4113_; 
v___x_4110_ = l_Lean_MessageData_ofFormat(v___x_4109_);
lean_inc(v_ref_4106_);
v___x_4111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4111_, 0, v_ref_4106_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4111_);
v___x_4113_ = v___x_4104_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
}
}
else
{
lean_object* v___x_4118_; uint8_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec(v_val_4094_);
v___x_4118_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4119_ = 0;
v___x_4120_ = l_Lean_MessageData_ofConstName(v_declName_4081_, v___x_4119_);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4118_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4123_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
return v___x_4124_;
}
}
else
{
lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
lean_dec(v_a_4093_);
v___x_4125_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4126_ = 0;
v___x_4127_ = l_Lean_MessageData_ofConstName(v_declName_4081_, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4125_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4130_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
return v___x_4131_;
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_declName_4081_);
v_a_4132_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4134_ = v___x_4092_;
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4092_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4144_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v_ref_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4142_; 
v_ref_4136_ = lean_ctor_get(v_a_4086_, 5);
v___x_4137_ = lean_io_error_to_string(v_a_4132_);
v___x_4138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
v___x_4139_ = l_Lean_MessageData_ofFormat(v___x_4138_);
lean_inc(v_ref_4136_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v_ref_4136_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4140_);
v___x_4142_ = v___x_4134_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_makeDocStringVerso(v_declName_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4154_, lean_object* v_k_4155_, lean_object* v_t_4156_, lean_object* v_h_4157_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4155_, v_t_4156_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4159_, lean_object* v_k_4160_, lean_object* v_t_4161_, lean_object* v_h_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4159_, v_k_4160_, v_t_4161_, v_h_4162_);
lean_dec(v_k_4160_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4164_, lean_object* v_binders_4165_, lean_object* v_docComment_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_){
_start:
{
uint8_t v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = l_Lean_isVersoDocComment(v_docComment_4166_);
v___x_4175_ = l_Lean_addDocStringOf(v___x_4174_, v_declName_4164_, v_binders_4165_, v_docComment_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4176_, lean_object* v_binders_4177_, lean_object* v_docComment_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_addDocString(v_declName_4176_, v_binders_4177_, v_docComment_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
lean_dec(v_a_4184_);
lean_dec_ref(v_a_4183_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4187_, lean_object* v_binders_4188_, lean_object* v_docString_x3f_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4189_) == 0)
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
lean_dec(v_binders_4188_);
lean_dec(v_declName_4187_);
v___x_4197_ = lean_box(0);
v___x_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
return v___x_4198_;
}
else
{
lean_object* v_val_4199_; lean_object* v___x_4200_; 
v_val_4199_ = lean_ctor_get(v_docString_x3f_4189_, 0);
lean_inc(v_val_4199_);
lean_dec_ref_known(v_docString_x3f_4189_, 1);
v___x_4200_ = l_Lean_addDocString(v_declName_4187_, v_binders_4188_, v_val_4199_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4201_, lean_object* v_binders_4202_, lean_object* v_docString_x3f_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_addDocString_x27(v_declName_4201_, v_binders_4202_, v_docString_x3f_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; lean_object* v_nextMacroScope_4217_; lean_object* v_ngen_4218_; lean_object* v_auxDeclNGen_4219_; lean_object* v_traceState_4220_; lean_object* v_messages_4221_; lean_object* v_infoState_4222_; lean_object* v_snapshotTasks_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4249_; 
v___x_4216_ = lean_st_ref_take(v___y_4214_);
v_nextMacroScope_4217_ = lean_ctor_get(v___x_4216_, 1);
v_ngen_4218_ = lean_ctor_get(v___x_4216_, 2);
v_auxDeclNGen_4219_ = lean_ctor_get(v___x_4216_, 3);
v_traceState_4220_ = lean_ctor_get(v___x_4216_, 4);
v_messages_4221_ = lean_ctor_get(v___x_4216_, 6);
v_infoState_4222_ = lean_ctor_get(v___x_4216_, 7);
v_snapshotTasks_4223_ = lean_ctor_get(v___x_4216_, 8);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; lean_object* v_unused_4251_; 
v_unused_4250_ = lean_ctor_get(v___x_4216_, 5);
lean_dec(v_unused_4250_);
v_unused_4251_ = lean_ctor_get(v___x_4216_, 0);
lean_dec(v_unused_4251_);
v___x_4225_ = v___x_4216_;
v_isShared_4226_ = v_isSharedCheck_4249_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_snapshotTasks_4223_);
lean_inc(v_infoState_4222_);
lean_inc(v_messages_4221_);
lean_inc(v_traceState_4220_);
lean_inc(v_auxDeclNGen_4219_);
lean_inc(v_ngen_4218_);
lean_inc(v_nextMacroScope_4217_);
lean_dec(v___x_4216_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4249_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 5, v___x_4227_);
lean_ctor_set(v___x_4225_, 0, v_env_4212_);
v___x_4229_ = v___x_4225_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_env_4212_);
lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_nextMacroScope_4217_);
lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_ngen_4218_);
lean_ctor_set(v_reuseFailAlloc_4248_, 3, v_auxDeclNGen_4219_);
lean_ctor_set(v_reuseFailAlloc_4248_, 4, v_traceState_4220_);
lean_ctor_set(v_reuseFailAlloc_4248_, 5, v___x_4227_);
lean_ctor_set(v_reuseFailAlloc_4248_, 6, v_messages_4221_);
lean_ctor_set(v_reuseFailAlloc_4248_, 7, v_infoState_4222_);
lean_ctor_set(v_reuseFailAlloc_4248_, 8, v_snapshotTasks_4223_);
v___x_4229_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v_mctx_4232_; lean_object* v_zetaDeltaFVarIds_4233_; lean_object* v_postponed_4234_; lean_object* v_diag_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4246_; 
v___x_4230_ = lean_st_ref_put(v___y_4214_, v___x_4229_);
v___x_4231_ = lean_st_ref_take(v___y_4213_);
v_mctx_4232_ = lean_ctor_get(v___x_4231_, 0);
v_zetaDeltaFVarIds_4233_ = lean_ctor_get(v___x_4231_, 2);
v_postponed_4234_ = lean_ctor_get(v___x_4231_, 3);
v_diag_4235_ = lean_ctor_get(v___x_4231_, 4);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v___x_4231_, 1);
lean_dec(v_unused_4247_);
v___x_4237_ = v___x_4231_;
v_isShared_4238_ = v_isSharedCheck_4246_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_diag_4235_);
lean_inc(v_postponed_4234_);
lean_inc(v_zetaDeltaFVarIds_4233_);
lean_inc(v_mctx_4232_);
lean_dec(v___x_4231_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4246_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
v___x_4239_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4238_ == 0)
{
lean_ctor_set(v___x_4237_, 1, v___x_4239_);
v___x_4241_ = v___x_4237_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_mctx_4232_);
lean_ctor_set(v_reuseFailAlloc_4245_, 1, v___x_4239_);
lean_ctor_set(v_reuseFailAlloc_4245_, 2, v_zetaDeltaFVarIds_4233_);
lean_ctor_set(v_reuseFailAlloc_4245_, 3, v_postponed_4234_);
lean_ctor_set(v_reuseFailAlloc_4245_, 4, v_diag_4235_);
v___x_4241_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = lean_st_ref_put(v___y_4213_, v___x_4241_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
return v___x_4244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec(v___y_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4257_, lean_object* v_as_4258_, size_t v_i_4259_, size_t v_stop_4260_, lean_object* v_b_4261_){
_start:
{
uint8_t v___x_4262_; 
v___x_4262_ = lean_usize_dec_eq(v_i_4259_, v_stop_4260_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v_index_4264_; lean_object* v_sourceString_4265_; lean_object* v_imports_4266_; lean_object* v_currNamespace_4267_; lean_object* v_openDecls_4268_; lean_object* v_options_4269_; lean_object* v_check_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4286_; 
v___x_4263_ = lean_array_uget(v_as_4258_, v_i_4259_);
v_index_4264_ = lean_ctor_get(v___x_4263_, 1);
v_sourceString_4265_ = lean_ctor_get(v___x_4263_, 2);
v_imports_4266_ = lean_ctor_get(v___x_4263_, 3);
v_currNamespace_4267_ = lean_ctor_get(v___x_4263_, 4);
v_openDecls_4268_ = lean_ctor_get(v___x_4263_, 5);
v_options_4269_ = lean_ctor_get(v___x_4263_, 6);
v_check_4270_ = lean_ctor_get(v___x_4263_, 7);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v___x_4263_, 0);
lean_dec(v_unused_4287_);
v___x_4272_ = v___x_4263_;
v_isShared_4273_ = v_isSharedCheck_4286_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_check_4270_);
lean_inc(v_options_4269_);
lean_inc(v_openDecls_4268_);
lean_inc(v_currNamespace_4267_);
lean_inc(v_imports_4266_);
lean_inc(v_sourceString_4265_);
lean_inc(v_index_4264_);
lean_dec(v___x_4263_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4286_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4274_; lean_object* v_toEnvExtension_4275_; lean_object* v_asyncMode_4276_; lean_object* v___x_4277_; lean_object* v___x_4279_; 
v___x_4274_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4275_ = lean_ctor_get(v___x_4274_, 0);
v_asyncMode_4276_ = lean_ctor_get(v_toEnvExtension_4275_, 2);
lean_inc(v_n_4257_);
v___x_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_n_4257_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4277_);
v___x_4279_ = v___x_4272_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_index_4264_);
lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_sourceString_4265_);
lean_ctor_set(v_reuseFailAlloc_4285_, 3, v_imports_4266_);
lean_ctor_set(v_reuseFailAlloc_4285_, 4, v_currNamespace_4267_);
lean_ctor_set(v_reuseFailAlloc_4285_, 5, v_openDecls_4268_);
lean_ctor_set(v_reuseFailAlloc_4285_, 6, v_options_4269_);
lean_ctor_set(v_reuseFailAlloc_4285_, 7, v_check_4270_);
v___x_4279_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; size_t v___x_4282_; size_t v___x_4283_; 
v___x_4280_ = lean_box(0);
v___x_4281_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4274_, v_b_4261_, v___x_4279_, v_asyncMode_4276_, v___x_4280_);
v___x_4282_ = ((size_t)1ULL);
v___x_4283_ = lean_usize_add(v_i_4259_, v___x_4282_);
v_i_4259_ = v___x_4283_;
v_b_4261_ = v___x_4281_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4257_);
return v_b_4261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4288_, lean_object* v_as_4289_, lean_object* v_i_4290_, lean_object* v_stop_4291_, lean_object* v_b_4292_){
_start:
{
size_t v_i_boxed_4293_; size_t v_stop_boxed_4294_; lean_object* v_res_4295_; 
v_i_boxed_4293_ = lean_unbox_usize(v_i_4290_);
lean_dec(v_i_4290_);
v_stop_boxed_4294_ = lean_unbox_usize(v_stop_4291_);
lean_dec(v_stop_4291_);
v_res_4295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4288_, v_as_4289_, v_i_boxed_4293_, v_stop_boxed_4294_, v_b_4292_);
lean_dec_ref(v_as_4289_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4296_, lean_object* v_deferred_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; lean_object* v_env_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4305_ = lean_st_ref_get(v___y_4303_);
v_env_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc_ref(v_env_4306_);
lean_dec(v___x_4305_);
v___x_4307_ = l_Lean_getMainModuleDoc(v_env_4306_);
v___x_4308_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4307_);
lean_dec_ref(v___x_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec_ref(v_docs_4296_);
v___x_4309_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4310_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4309_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4310_;
}
else
{
lean_object* v___x_4311_; lean_object* v_env_4312_; lean_object* v___x_4313_; lean_object* v_size_4314_; lean_object* v___x_4315_; lean_object* v_env_4316_; lean_object* v___x_4317_; 
v___x_4311_ = lean_st_ref_get(v___y_4303_);
v_env_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc_ref(v_env_4312_);
lean_dec(v___x_4311_);
v___x_4313_ = l_Lean_getMainVersoModuleDocs(v_env_4312_);
v_size_4314_ = lean_ctor_get(v___x_4313_, 2);
lean_inc(v_size_4314_);
lean_dec_ref(v___x_4313_);
v___x_4315_ = lean_st_ref_get(v___y_4303_);
v_env_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_ref(v_env_4316_);
lean_dec(v___x_4315_);
v___x_4317_ = l_Lean_addVersoModuleDocSnippet(v_env_4316_, v_docs_4296_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
lean_dec(v_size_4314_);
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4320_ = l_Lean_stringToMessageData(v_a_4318_);
v___x_4321_ = l_Lean_indentD(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4319_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4322_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4323_;
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; 
v_a_4324_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4325_ = lean_unsigned_to_nat(0u);
v___x_4326_ = lean_array_get_size(v_deferred_4297_);
v___x_4327_ = lean_nat_dec_lt(v___x_4325_, v___x_4326_);
if (v___x_4327_ == 0)
{
lean_object* v___x_4328_; 
lean_dec(v_size_4314_);
v___x_4328_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4324_, v___y_4301_, v___y_4303_);
return v___x_4328_;
}
else
{
size_t v___x_4329_; size_t v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4329_ = ((size_t)0ULL);
v___x_4330_ = lean_usize_of_nat(v___x_4326_);
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4314_, v_deferred_4297_, v___x_4329_, v___x_4330_, v_a_4324_);
v___x_4332_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4331_, v___y_4301_, v___y_4303_);
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4333_, lean_object* v_deferred_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4333_, v_deferred_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec_ref(v_deferred_4334_);
return v_res_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4343_, lean_object* v_docComment_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = l_Lean_versoModDocString(v_range_4343_, v_docComment_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v_fst_4354_; lean_object* v_snd_4355_; lean_object* v___x_4356_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v_fst_4354_ = lean_ctor_get(v_a_4353_, 0);
lean_inc(v_fst_4354_);
v_snd_4355_ = lean_ctor_get(v_a_4353_, 1);
lean_inc(v_snd_4355_);
lean_dec(v_a_4353_);
v___x_4356_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4354_, v_snd_4355_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
lean_dec(v_snd_4355_);
return v___x_4356_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_a_4357_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4352_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4352_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4365_, lean_object* v_docComment_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_addVersoModDocString(v_range_4365_, v_docComment_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_docComment_4366_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4375_, v___y_4379_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
lean_dec(v___y_4388_);
lean_dec_ref(v___y_4387_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
return v_res_4392_;
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
