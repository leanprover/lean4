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
lean_object* v_toCold_826_; lean_object* v_val_827_; lean_object* v_options_828_; lean_object* v_currRecDepth_829_; lean_object* v_maxRecDepth_830_; lean_object* v_ref_831_; lean_object* v_currNamespace_832_; lean_object* v_openDecls_833_; lean_object* v_initHeartbeats_834_; lean_object* v_maxHeartbeats_835_; lean_object* v_currMacroScope_836_; uint8_t v_diag_837_; uint8_t v_suppressElabErrors_838_; lean_object* v_fileName_839_; lean_object* v_quotContext_840_; lean_object* v_cancelTk_x3f_841_; lean_object* v_inheritedTraceOptions_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_toCold_826_ = lean_ctor_get(v___y_822_, 0);
v_val_827_ = lean_ctor_get(v_fileMap_x3f_813_, 0);
v_options_828_ = lean_ctor_get(v___y_822_, 1);
v_currRecDepth_829_ = lean_ctor_get(v___y_822_, 2);
v_maxRecDepth_830_ = lean_ctor_get(v___y_822_, 3);
v_ref_831_ = lean_ctor_get(v___y_822_, 4);
v_currNamespace_832_ = lean_ctor_get(v___y_822_, 5);
v_openDecls_833_ = lean_ctor_get(v___y_822_, 6);
v_initHeartbeats_834_ = lean_ctor_get(v___y_822_, 7);
v_maxHeartbeats_835_ = lean_ctor_get(v___y_822_, 8);
v_currMacroScope_836_ = lean_ctor_get(v___y_822_, 9);
v_diag_837_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*10);
v_suppressElabErrors_838_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*10 + 1);
v_fileName_839_ = lean_ctor_get(v_toCold_826_, 0);
v_quotContext_840_ = lean_ctor_get(v_toCold_826_, 2);
v_cancelTk_x3f_841_ = lean_ctor_get(v_toCold_826_, 3);
v_inheritedTraceOptions_842_ = lean_ctor_get(v_toCold_826_, 4);
lean_inc_ref(v_inheritedTraceOptions_842_);
lean_inc(v_cancelTk_x3f_841_);
lean_inc(v_quotContext_840_);
lean_inc(v_val_827_);
lean_inc_ref(v_fileName_839_);
v___x_843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_843_, 0, v_fileName_839_);
lean_ctor_set(v___x_843_, 1, v_val_827_);
lean_ctor_set(v___x_843_, 2, v_quotContext_840_);
lean_ctor_set(v___x_843_, 3, v_cancelTk_x3f_841_);
lean_ctor_set(v___x_843_, 4, v_inheritedTraceOptions_842_);
lean_inc(v_currMacroScope_836_);
lean_inc(v_maxHeartbeats_835_);
lean_inc(v_initHeartbeats_834_);
lean_inc(v_openDecls_833_);
lean_inc(v_currNamespace_832_);
lean_inc(v_ref_831_);
lean_inc(v_maxRecDepth_830_);
lean_inc(v_currRecDepth_829_);
lean_inc_ref(v_options_828_);
v___x_844_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_844_, 0, v___x_843_);
lean_ctor_set(v___x_844_, 1, v_options_828_);
lean_ctor_set(v___x_844_, 2, v_currRecDepth_829_);
lean_ctor_set(v___x_844_, 3, v_maxRecDepth_830_);
lean_ctor_set(v___x_844_, 4, v_ref_831_);
lean_ctor_set(v___x_844_, 5, v_currNamespace_832_);
lean_ctor_set(v___x_844_, 6, v_openDecls_833_);
lean_ctor_set(v___x_844_, 7, v_initHeartbeats_834_);
lean_ctor_set(v___x_844_, 8, v_maxHeartbeats_835_);
lean_ctor_set(v___x_844_, 9, v_currMacroScope_836_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*10, v_diag_837_);
lean_ctor_set_uint8(v___x_844_, sizeof(void*)*10 + 1, v_suppressElabErrors_838_);
v___x_845_ = l_Lean_Doc_DocM_exec___redArg(v_declName_814_, v_binders_815_, v___x_816_, v___x_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___x_844_, v___y_823_);
lean_dec_ref_known(v___x_844_, 10);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_846_, lean_object* v_declName_847_, lean_object* v_binders_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
uint8_t v___x_9698__boxed_858_; lean_object* v_res_859_; 
v___x_9698__boxed_858_ = lean_unbox(v___x_850_);
v_res_859_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_846_, v_declName_847_, v_binders_848_, v___x_849_, v___x_9698__boxed_858_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
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
lean_object* v___x_897_; lean_object* v_env_898_; lean_object* v___x_899_; lean_object* v_mctx_900_; lean_object* v_lctx_901_; lean_object* v_options_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_897_ = lean_st_ref_get(v___y_895_);
v_env_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc_ref(v_env_898_);
lean_dec(v___x_897_);
v___x_899_ = lean_st_ref_get(v___y_893_);
v_mctx_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_mctx_900_);
lean_dec(v___x_899_);
v_lctx_901_ = lean_ctor_get(v___y_892_, 2);
v_options_902_ = lean_ctor_get(v___y_894_, 1);
lean_inc_ref(v_options_902_);
lean_inc_ref(v_lctx_901_);
v___x_903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_903_, 0, v_env_898_);
lean_ctor_set(v___x_903_, 1, v_mctx_900_);
lean_ctor_set(v___x_903_, 2, v_lctx_901_);
lean_ctor_set(v___x_903_, 3, v_options_902_);
v___x_904_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_msgData_891_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_912_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_921_, uint8_t v___y_922_, lean_object* v_x_923_){
_start:
{
if (lean_obj_tag(v_x_923_) == 1)
{
lean_object* v_pre_924_; 
v_pre_924_ = lean_ctor_get(v_x_923_, 0);
switch(lean_obj_tag(v_pre_924_))
{
case 1:
{
lean_object* v_pre_925_; 
v_pre_925_ = lean_ctor_get(v_pre_924_, 0);
switch(lean_obj_tag(v_pre_925_))
{
case 0:
{
lean_object* v_str_926_; lean_object* v_str_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_str_926_ = lean_ctor_get(v_x_923_, 1);
v_str_927_ = lean_ctor_get(v_pre_924_, 1);
v___x_928_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_929_ = lean_string_dec_eq(v_str_927_, v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_931_ = lean_string_dec_eq(v_str_927_, v___x_930_);
if (v___x_931_ == 0)
{
return v___x_931_;
}
else
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_933_ = lean_string_dec_eq(v_str_926_, v___x_932_);
if (v___x_933_ == 0)
{
return v___x_933_;
}
else
{
return v_suppressElabErrors_921_;
}
}
}
else
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_935_ = lean_string_dec_eq(v_str_926_, v___x_934_);
if (v___x_935_ == 0)
{
return v___x_935_;
}
else
{
return v_suppressElabErrors_921_;
}
}
}
case 1:
{
lean_object* v_pre_936_; 
v_pre_936_ = lean_ctor_get(v_pre_925_, 0);
if (lean_obj_tag(v_pre_936_) == 0)
{
lean_object* v_str_937_; lean_object* v_str_938_; lean_object* v_str_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_str_937_ = lean_ctor_get(v_x_923_, 1);
v_str_938_ = lean_ctor_get(v_pre_924_, 1);
v_str_939_ = lean_ctor_get(v_pre_925_, 1);
v___x_940_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_941_ = lean_string_dec_eq(v_str_939_, v___x_940_);
if (v___x_941_ == 0)
{
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_943_ = lean_string_dec_eq(v_str_938_, v___x_942_);
if (v___x_943_ == 0)
{
return v___x_943_;
}
else
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_945_ = lean_string_dec_eq(v_str_937_, v___x_944_);
if (v___x_945_ == 0)
{
return v___x_945_;
}
else
{
return v_suppressElabErrors_921_;
}
}
}
}
else
{
return v___y_922_;
}
}
default: 
{
return v___y_922_;
}
}
}
case 0:
{
lean_object* v_str_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_str_946_ = lean_ctor_get(v_x_923_, 1);
v___x_947_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_948_ = lean_string_dec_eq(v_str_946_, v___x_947_);
if (v___x_948_ == 0)
{
return v___x_948_;
}
else
{
return v_suppressElabErrors_921_;
}
}
default: 
{
return v___y_922_;
}
}
}
else
{
return v___y_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_949_, lean_object* v___y_950_, lean_object* v_x_951_){
_start:
{
uint8_t v_suppressElabErrors_boxed_952_; uint8_t v___y_9797__boxed_953_; uint8_t v_res_954_; lean_object* v_r_955_; 
v_suppressElabErrors_boxed_952_ = lean_unbox(v_suppressElabErrors_949_);
v___y_9797__boxed_953_ = lean_unbox(v___y_950_);
v_res_954_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_952_, v___y_9797__boxed_953_, v_x_951_);
lean_dec(v_x_951_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_956_, lean_object* v_msgData_957_, uint8_t v_severity_958_, uint8_t v_isSilent_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___y_966_; uint8_t v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; uint8_t v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_1002_; lean_object* v___y_1003_; uint8_t v___y_1004_; uint8_t v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1028_; uint8_t v___y_1029_; uint8_t v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; uint8_t v___x_1048_; lean_object* v___y_1050_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1053_; uint8_t v___y_1054_; uint8_t v___y_1055_; uint8_t v___y_1057_; uint8_t v___x_1071_; 
v___x_1048_ = 2;
v___x_1071_ = l_Lean_instBEqMessageSeverity_beq(v_severity_958_, v___x_1048_);
if (v___x_1071_ == 0)
{
v___y_1057_ = v___x_1071_;
goto v___jp_1056_;
}
else
{
uint8_t v___x_1072_; 
lean_inc_ref(v_msgData_957_);
v___x_1072_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_957_);
v___y_1057_ = v___x_1072_;
goto v___jp_1056_;
}
v___jp_965_:
{
lean_object* v___x_975_; lean_object* v_currNamespace_976_; lean_object* v_openDecls_977_; lean_object* v_env_978_; lean_object* v_nextMacroScope_979_; lean_object* v_ngen_980_; lean_object* v_auxDeclNGen_981_; lean_object* v_traceState_982_; lean_object* v_cache_983_; lean_object* v_messages_984_; lean_object* v_infoState_985_; lean_object* v_snapshotTasks_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v___x_975_ = lean_st_ref_take(v___y_974_);
v_currNamespace_976_ = lean_ctor_get(v___y_973_, 5);
v_openDecls_977_ = lean_ctor_get(v___y_973_, 6);
v_env_978_ = lean_ctor_get(v___x_975_, 0);
v_nextMacroScope_979_ = lean_ctor_get(v___x_975_, 1);
v_ngen_980_ = lean_ctor_get(v___x_975_, 2);
v_auxDeclNGen_981_ = lean_ctor_get(v___x_975_, 3);
v_traceState_982_ = lean_ctor_get(v___x_975_, 4);
v_cache_983_ = lean_ctor_get(v___x_975_, 5);
v_messages_984_ = lean_ctor_get(v___x_975_, 6);
v_infoState_985_ = lean_ctor_get(v___x_975_, 7);
v_snapshotTasks_986_ = lean_ctor_get(v___x_975_, 8);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v___x_975_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snapshotTasks_986_);
lean_inc(v_infoState_985_);
lean_inc(v_messages_984_);
lean_inc(v_cache_983_);
lean_inc(v_traceState_982_);
lean_inc(v_auxDeclNGen_981_);
lean_inc(v_ngen_980_);
lean_inc(v_nextMacroScope_979_);
lean_inc(v_env_978_);
lean_dec(v___x_975_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
lean_inc(v_openDecls_977_);
lean_inc(v_currNamespace_976_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_currNamespace_976_);
lean_ctor_set(v___x_990_, 1, v_openDecls_977_);
v___x_991_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___y_971_);
lean_inc_ref(v___y_972_);
lean_inc_ref(v___y_969_);
v___x_992_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_992_, 0, v___y_969_);
lean_ctor_set(v___x_992_, 1, v___y_966_);
lean_ctor_set(v___x_992_, 2, v___y_968_);
lean_ctor_set(v___x_992_, 3, v___y_972_);
lean_ctor_set(v___x_992_, 4, v___x_991_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*5, v___y_967_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*5 + 1, v___y_970_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*5 + 2, v_isSilent_959_);
v___x_993_ = l_Lean_MessageLog_add(v___x_992_, v_messages_984_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 6, v___x_993_);
v___x_995_ = v___x_988_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_env_978_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_nextMacroScope_979_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_ngen_980_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_auxDeclNGen_981_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_traceState_982_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_cache_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 6, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_999_, 7, v_infoState_985_);
lean_ctor_set(v_reuseFailAlloc_999_, 8, v_snapshotTasks_986_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_996_ = lean_st_ref_put(v___y_974_, v___x_995_);
v___x_997_ = lean_box(0);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
return v___x_998_;
}
}
}
v___jp_1001_:
{
lean_object* v_fileName_1009_; lean_object* v_fileMap_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1026_; 
v_fileName_1009_ = lean_ctor_get(v___y_1007_, 0);
v_fileMap_1010_ = lean_ctor_get(v___y_1007_, 1);
v___x_1011_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_957_);
v___x_1012_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_1011_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1026_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_inc_ref_n(v_fileMap_1010_, 2);
v___x_1017_ = l_Lean_FileMap_toPosition(v_fileMap_1010_, v___y_1003_);
lean_dec(v___y_1003_);
v___x_1018_ = l_Lean_FileMap_toPosition(v_fileMap_1010_, v___y_1008_);
lean_dec(v___y_1008_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1005_ == 0)
{
lean_del_object(v___x_1015_);
lean_dec_ref(v___y_1002_);
v___y_966_ = v___x_1017_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___x_1019_;
v___y_969_ = v_fileName_1009_;
v___y_970_ = v___y_1006_;
v___y_971_ = v_a_1013_;
v___y_972_ = v___x_1020_;
v___y_973_ = v___y_962_;
v___y_974_ = v___y_963_;
goto v___jp_965_;
}
else
{
uint8_t v___x_1021_; 
lean_inc(v_a_1013_);
v___x_1021_ = l_Lean_MessageData_hasTag(v___y_1002_, v_a_1013_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec_ref_known(v___x_1019_, 1);
lean_dec_ref(v___x_1017_);
lean_dec(v_a_1013_);
v___x_1022_ = lean_box(0);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1022_);
v___x_1024_ = v___x_1015_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_del_object(v___x_1015_);
v___y_966_ = v___x_1017_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___x_1019_;
v___y_969_ = v_fileName_1009_;
v___y_970_ = v___y_1006_;
v___y_971_ = v_a_1013_;
v___y_972_ = v___x_1020_;
v___y_973_ = v___y_962_;
v___y_974_ = v___y_963_;
goto v___jp_965_;
}
}
}
}
v___jp_1027_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Syntax_getTailPos_x3f(v___y_1032_, v___y_1029_);
lean_dec(v___y_1032_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_inc(v___y_1034_);
v___y_1002_ = v___y_1028_;
v___y_1003_ = v___y_1034_;
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1031_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v___y_1033_;
v___y_1008_ = v___y_1034_;
goto v___jp_1001_;
}
else
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___y_1002_ = v___y_1028_;
v___y_1003_ = v___y_1034_;
v___y_1004_ = v___y_1029_;
v___y_1005_ = v___y_1031_;
v___y_1006_ = v___y_1030_;
v___y_1007_ = v___y_1033_;
v___y_1008_ = v_val_1036_;
goto v___jp_1001_;
}
}
v___jp_1037_:
{
lean_object* v_ref_1044_; lean_object* v___x_1045_; 
v_ref_1044_ = l_Lean_replaceRef(v_ref_956_, v___y_1039_);
v___x_1045_ = l_Lean_Syntax_getPos_x3f(v_ref_1044_, v___y_1040_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___y_1028_ = v___y_1038_;
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___y_1041_;
v___y_1032_ = v_ref_1044_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v___x_1046_;
goto v___jp_1027_;
}
else
{
lean_object* v_val_1047_; 
v_val_1047_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_val_1047_);
lean_dec_ref_known(v___x_1045_, 1);
v___y_1028_ = v___y_1038_;
v___y_1029_ = v___y_1040_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___y_1041_;
v___y_1032_ = v_ref_1044_;
v___y_1033_ = v___y_1042_;
v___y_1034_ = v_val_1047_;
goto v___jp_1027_;
}
}
v___jp_1049_:
{
if (v___y_1055_ == 0)
{
v___y_1038_ = v___y_1051_;
v___y_1039_ = v___y_1050_;
v___y_1040_ = v___y_1054_;
v___y_1041_ = v___y_1052_;
v___y_1042_ = v___y_1053_;
v___y_1043_ = v_severity_958_;
goto v___jp_1037_;
}
else
{
v___y_1038_ = v___y_1051_;
v___y_1039_ = v___y_1050_;
v___y_1040_ = v___y_1054_;
v___y_1041_ = v___y_1052_;
v___y_1042_ = v___y_1053_;
v___y_1043_ = v___x_1048_;
goto v___jp_1037_;
}
}
v___jp_1056_:
{
if (v___y_1057_ == 0)
{
lean_object* v_toCold_1058_; lean_object* v_options_1059_; lean_object* v_ref_1060_; uint8_t v_suppressElabErrors_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___f_1064_; uint8_t v___x_1065_; uint8_t v___x_1066_; 
v_toCold_1058_ = lean_ctor_get(v___y_962_, 0);
v_options_1059_ = lean_ctor_get(v___y_962_, 1);
v_ref_1060_ = lean_ctor_get(v___y_962_, 4);
v_suppressElabErrors_1061_ = lean_ctor_get_uint8(v___y_962_, sizeof(void*)*10 + 1);
v___x_1062_ = lean_box(v_suppressElabErrors_1061_);
v___x_1063_ = lean_box(v___y_1057_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1064_, 0, v___x_1062_);
lean_closure_set(v___f_1064_, 1, v___x_1063_);
v___x_1065_ = 1;
v___x_1066_ = l_Lean_instBEqMessageSeverity_beq(v_severity_958_, v___x_1065_);
if (v___x_1066_ == 0)
{
v___y_1050_ = v_ref_1060_;
v___y_1051_ = v___f_1064_;
v___y_1052_ = v_suppressElabErrors_1061_;
v___y_1053_ = v_toCold_1058_;
v___y_1054_ = v___y_1057_;
v___y_1055_ = v___x_1066_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = l_Lean_warningAsError;
v___x_1068_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1059_, v___x_1067_);
v___y_1050_ = v_ref_1060_;
v___y_1051_ = v___f_1064_;
v___y_1052_ = v_suppressElabErrors_1061_;
v___y_1053_ = v_toCold_1058_;
v___y_1054_ = v___y_1057_;
v___y_1055_ = v___x_1068_;
goto v___jp_1049_;
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v_msgData_957_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1073_, lean_object* v_msgData_1074_, lean_object* v_severity_1075_, lean_object* v_isSilent_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
uint8_t v_severity_boxed_1082_; uint8_t v_isSilent_boxed_1083_; lean_object* v_res_1084_; 
v_severity_boxed_1082_ = lean_unbox(v_severity_1075_);
v_isSilent_boxed_1083_ = lean_unbox(v_isSilent_1076_);
v_res_1084_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1073_, v_msgData_1074_, v_severity_boxed_1082_, v_isSilent_boxed_1083_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_ref_1073_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1085_, size_t v_sz_1086_, size_t v_i_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_usize_dec_lt(v_i_1087_, v_sz_1086_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_b_1088_);
return v___x_1097_;
}
else
{
lean_object* v_ref_1098_; lean_object* v_a_1099_; uint8_t v_severity_1100_; uint8_t v_isSilent_1101_; lean_object* v_data_1102_; lean_object* v___x_1103_; 
v_ref_1098_ = lean_ctor_get(v___y_1093_, 4);
v_a_1099_ = lean_array_uget_borrowed(v_as_1085_, v_i_1087_);
v_severity_1100_ = lean_ctor_get_uint8(v_a_1099_, sizeof(void*)*5 + 1);
v_isSilent_1101_ = lean_ctor_get_uint8(v_a_1099_, sizeof(void*)*5 + 2);
v_data_1102_ = lean_ctor_get(v_a_1099_, 4);
lean_inc(v_data_1102_);
v___x_1103_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1098_, v_data_1102_, v_severity_1100_, v_isSilent_1101_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; 
lean_dec_ref_known(v___x_1103_, 1);
v___x_1104_ = lean_box(0);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_add(v_i_1087_, v___x_1105_);
v_i_1087_ = v___x_1106_;
v_b_1088_ = v___x_1104_;
goto _start;
}
else
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1108_, lean_object* v_sz_1109_, lean_object* v_i_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
size_t v_sz_boxed_1119_; size_t v_i_boxed_1120_; lean_object* v_res_1121_; 
v_sz_boxed_1119_ = lean_unbox_usize(v_sz_1109_);
lean_dec(v_sz_1109_);
v_i_boxed_1120_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_res_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1108_, v_sz_boxed_1119_, v_i_boxed_1120_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec_ref(v_as_1108_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v_infoState_1126_; lean_object* v_env_1127_; lean_object* v_nextMacroScope_1128_; lean_object* v_ngen_1129_; lean_object* v_auxDeclNGen_1130_; lean_object* v_traceState_1131_; lean_object* v_cache_1132_; lean_object* v_messages_1133_; lean_object* v_snapshotTasks_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1154_; 
v___x_1125_ = lean_st_ref_take(v___y_1123_);
v_infoState_1126_ = lean_ctor_get(v___x_1125_, 7);
v_env_1127_ = lean_ctor_get(v___x_1125_, 0);
v_nextMacroScope_1128_ = lean_ctor_get(v___x_1125_, 1);
v_ngen_1129_ = lean_ctor_get(v___x_1125_, 2);
v_auxDeclNGen_1130_ = lean_ctor_get(v___x_1125_, 3);
v_traceState_1131_ = lean_ctor_get(v___x_1125_, 4);
v_cache_1132_ = lean_ctor_get(v___x_1125_, 5);
v_messages_1133_ = lean_ctor_get(v___x_1125_, 6);
v_snapshotTasks_1134_ = lean_ctor_get(v___x_1125_, 8);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1154_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snapshotTasks_1134_);
lean_inc(v_infoState_1126_);
lean_inc(v_messages_1133_);
lean_inc(v_cache_1132_);
lean_inc(v_traceState_1131_);
lean_inc(v_auxDeclNGen_1130_);
lean_inc(v_ngen_1129_);
lean_inc(v_nextMacroScope_1128_);
lean_inc(v_env_1127_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1154_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_assignment_1138_; lean_object* v_lazyAssignment_1139_; lean_object* v_trees_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1153_; 
v_assignment_1138_ = lean_ctor_get(v_infoState_1126_, 0);
v_lazyAssignment_1139_ = lean_ctor_get(v_infoState_1126_, 1);
v_trees_1140_ = lean_ctor_get(v_infoState_1126_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_infoState_1126_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1142_ = v_infoState_1126_;
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_trees_1140_);
lean_inc(v_lazyAssignment_1139_);
lean_inc(v_assignment_1138_);
lean_dec(v_infoState_1126_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_assignment_1138_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_lazyAssignment_1139_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_trees_1140_);
v___x_1145_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3, v_flag_1122_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 7, v___x_1145_);
v___x_1147_ = v___x_1136_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_env_1127_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_nextMacroScope_1128_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_ngen_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_auxDeclNGen_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v_traceState_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_cache_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_messages_1133_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_snapshotTasks_1134_);
v___x_1147_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_st_ref_put(v___y_1123_, v___x_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v_flag_boxed_1158_; lean_object* v_res_1159_; 
v_flag_boxed_1158_ = lean_unbox(v_flag_1155_);
v_res_1159_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1158_, v___y_1156_);
lean_dec(v___y_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; lean_object* v_infoState_1170_; uint8_t v_enabled_1171_; lean_object* v_a_1173_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1169_ = lean_st_ref_get(v___y_1167_);
v_infoState_1170_ = lean_ctor_get(v___x_1169_, 7);
lean_inc_ref(v_infoState_1170_);
lean_dec(v___x_1169_);
v_enabled_1171_ = lean_ctor_get_uint8(v_infoState_1170_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1170_);
v___x_1183_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1160_, v___y_1167_);
lean_dec_ref(v___x_1183_);
lean_inc(v___y_1167_);
lean_inc_ref(v___y_1166_);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
v___x_1184_ = lean_apply_7(v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, lean_box(0));
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1171_, v___y_1167_);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v___x_1186_, 0);
lean_dec(v_unused_1194_);
v___x_1188_ = v___x_1186_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v___x_1186_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_a_1185_);
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1185_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1184_, 1);
v_a_1173_ = v_a_1195_;
goto v___jp_1172_;
}
v___jp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
v___x_1174_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1171_, v___y_1167_);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; 
v_unused_1182_ = lean_ctor_get(v___x_1174_, 0);
lean_dec(v_unused_1182_);
v___x_1176_ = v___x_1174_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_dec(v___x_1174_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v_a_1173_);
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_flag_boxed_1205_; lean_object* v_res_1206_; 
v_flag_boxed_1205_ = lean_unbox(v_flag_1196_);
v_res_1206_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1205_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1207_, lean_object* v_binders_1208_, lean_object* v_blocks_1209_, lean_object* v_fileMap_x3f_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v_a_1221_; size_t v_sz_1239_; size_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___y_1245_; uint8_t v___x_1246_; lean_object* v___x_1247_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_sz_1239_ = lean_array_size(v_blocks_1209_);
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1239_, v___x_1240_, v_blocks_1209_);
v___x_1242_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1242_, 0, v___x_1241_);
v___x_1243_ = 1;
v___x_1244_ = lean_box(v___x_1243_);
v___y_1245_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1245_, 0, v_fileMap_x3f_1210_);
lean_closure_set(v___y_1245_, 1, v_declName_1207_);
lean_closure_set(v___y_1245_, 2, v_binders_1208_);
lean_closure_set(v___y_1245_, 3, v___x_1242_);
lean_closure_set(v___y_1245_, 4, v___x_1244_);
v___x_1246_ = 0;
v___x_1247_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1246_, v___y_1245_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___x_1249_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1216_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = l_Lean_Core_setMessageLog___redArg(v_a_1219_, v_a_1216_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; size_t v_sz_1254_; lean_object* v___x_1255_; 
lean_dec_ref_known(v___x_1251_, 1);
v___x_1252_ = l_Lean_MessageLog_toArray(v_a_1250_);
lean_dec(v_a_1250_);
v___x_1253_ = lean_box(0);
v_sz_1254_ = lean_array_size(v___x_1252_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1252_, v_sz_1254_, v___x_1240_, v___x_1253_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec_ref(v___x_1252_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1280_; 
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1281_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1280_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1280_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_fst_1259_; lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1279_; 
v_fst_1259_ = lean_ctor_get(v_a_1248_, 0);
v_snd_1260_ = lean_ctor_get(v_a_1248_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1262_ = v_a_1248_;
v_isShared_1263_ = v_isSharedCheck_1279_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_inc(v_fst_1259_);
lean_dec(v_a_1248_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1279_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1278_; 
v_fst_1264_ = lean_ctor_get(v_fst_1259_, 0);
v_snd_1265_ = lean_ctor_get(v_fst_1259_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_fst_1259_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1267_ = v_fst_1259_;
v_isShared_1268_ = v_isSharedCheck_1278_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snd_1265_);
lean_inc(v_fst_1264_);
lean_dec(v_fst_1259_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1278_;
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
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_fst_1264_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1265_);
v___x_1270_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1270_);
v___x_1272_ = v___x_1262_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_snd_1260_);
v___x_1272_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1274_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1272_);
v___x_1274_ = v___x_1257_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_a_1248_);
v_a_1282_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1255_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1255_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v_a_1250_);
lean_dec(v_a_1248_);
v_a_1290_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1251_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1251_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; 
lean_dec(v_a_1248_);
v_a_1298_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1249_, 1);
v_a_1221_ = v_a_1298_;
goto v___jp_1220_;
}
}
else
{
lean_object* v_a_1299_; 
v_a_1299_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1247_, 1);
v_a_1221_ = v_a_1299_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Core_setMessageLog___redArg(v_a_1219_, v_a_1216_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1230_);
v___x_1224_ = v___x_1222_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
lean_ctor_set(v___x_1224_, 0, v_a_1221_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1221_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec_ref(v_a_1221_);
v_a_1231_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1222_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1222_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_fileMap_x3f_1210_);
lean_dec_ref(v_blocks_1209_);
lean_dec(v_binders_1208_);
lean_dec(v_declName_1207_);
v_a_1300_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1218_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1218_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1308_, lean_object* v_binders_1309_, lean_object* v_blocks_1310_, lean_object* v_fileMap_x3f_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1308_, v_binders_1309_, v_blocks_1310_, v_fileMap_x3f_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_a_1313_);
lean_dec_ref(v_a_1312_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1320_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
uint8_t v_flag_boxed_1337_; lean_object* v_res_1338_; 
v_flag_boxed_1337_ = lean_unbox(v_flag_1329_);
v_res_1338_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1337_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1339_, uint8_t v_flag_1340_, lean_object* v_x_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1340_, v_x_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_flag_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_flag_boxed_1360_; lean_object* v_res_1361_; 
v_flag_boxed_1360_ = lean_unbox(v_flag_1351_);
v_res_1361_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1350_, v_flag_boxed_1360_, v_x_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1362_, lean_object* v_msgData_1363_, uint8_t v_severity_1364_, uint8_t v_isSilent_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1362_, v_msgData_1363_, v_severity_1364_, v_isSilent_1365_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1374_, lean_object* v_msgData_1375_, lean_object* v_severity_1376_, lean_object* v_isSilent_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_severity_boxed_1385_; uint8_t v_isSilent_boxed_1386_; lean_object* v_res_1387_; 
v_severity_boxed_1385_ = lean_unbox(v_severity_1376_);
v_isSilent_boxed_1386_ = lean_unbox(v_isSilent_1377_);
v_res_1387_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1374_, v_msgData_1375_, v_severity_boxed_1385_, v_isSilent_boxed_1386_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v_ref_1374_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1388_, uint8_t v_severity_1389_, uint8_t v_isSilent_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_ref_1396_; lean_object* v___x_1397_; 
v_ref_1396_ = lean_ctor_get(v___y_1393_, 4);
v___x_1397_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1396_, v_msgData_1388_, v_severity_1389_, v_isSilent_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1398_, lean_object* v_severity_1399_, lean_object* v_isSilent_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
uint8_t v_severity_boxed_1406_; uint8_t v_isSilent_boxed_1407_; lean_object* v_res_1408_; 
v_severity_boxed_1406_ = lean_unbox(v_severity_1399_);
v_isSilent_boxed_1407_ = lean_unbox(v_isSilent_1400_);
v_res_1408_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1398_, v_severity_boxed_1406_, v_isSilent_boxed_1407_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
uint8_t v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = 2;
v___x_1418_ = 0;
v___x_1419_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1409_, v___x_1417_, v___x_1418_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1429_, size_t v_sz_1430_, size_t v_i_1431_, lean_object* v_b_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_usize_dec_lt(v_i_1431_, v_sz_1430_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_b_1432_);
return v___x_1441_;
}
else
{
lean_object* v_a_1442_; lean_object* v_snd_1443_; lean_object* v_snd_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_a_1442_ = lean_array_uget_borrowed(v_as_1429_, v_i_1431_);
v_snd_1443_ = lean_ctor_get(v_a_1442_, 1);
v_snd_1444_ = lean_ctor_get(v_snd_1443_, 1);
lean_inc(v_snd_1444_);
v___x_1445_ = l_Lean_Parser_Error_toString(v_snd_1444_);
v___x_1446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
v___x_1447_ = l_Lean_MessageData_ofFormat(v___x_1446_);
v___x_1448_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1447_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; 
lean_dec_ref_known(v___x_1448_, 1);
v___x_1449_ = lean_box(0);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1431_, v___x_1450_);
v_i_1431_ = v___x_1451_;
v_b_1432_ = v___x_1449_;
goto _start;
}
else
{
return v___x_1448_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1453_, lean_object* v_sz_1454_, lean_object* v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1454_);
lean_dec(v_sz_1454_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1453_, v_sz_boxed_1464_, v_i_boxed_1465_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v_as_1453_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1484_, lean_object* v_binders_1485_, lean_object* v_docComment_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1494_; lean_object* v_toCold_1495_; lean_object* v_env_1496_; lean_object* v_options_1497_; lean_object* v_currNamespace_1498_; lean_object* v_openDecls_1499_; lean_object* v_fileName_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1494_ = lean_st_ref_get(v_a_1492_);
v_toCold_1495_ = lean_ctor_get(v_a_1491_, 0);
v_env_1496_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref_n(v_env_1496_, 2);
lean_dec(v___x_1494_);
v_options_1497_ = lean_ctor_get(v_a_1491_, 1);
v_currNamespace_1498_ = lean_ctor_get(v_a_1491_, 5);
v_openDecls_1499_ = lean_ctor_get(v_a_1491_, 6);
v_fileName_1500_ = lean_ctor_get(v_toCold_1495_, 0);
v___x_1501_ = lean_string_utf8_byte_size(v_docComment_1486_);
lean_inc_ref_n(v_docComment_1486_, 2);
v___x_1502_ = l_Lean_FileMap_ofString(v_docComment_1486_);
lean_inc_ref(v___x_1502_);
lean_inc_ref(v_fileName_1500_);
v___x_1503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1503_, 0, v_docComment_1486_);
lean_ctor_set(v___x_1503_, 1, v_fileName_1500_);
lean_ctor_set(v___x_1503_, 2, v___x_1502_);
lean_ctor_set(v___x_1503_, 3, v___x_1501_);
lean_inc(v_openDecls_1499_);
lean_inc(v_currNamespace_1498_);
lean_inc_ref(v_options_1497_);
v___x_1504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1504_, 0, v_env_1496_);
lean_ctor_set(v___x_1504_, 1, v_options_1497_);
lean_ctor_set(v___x_1504_, 2, v_currNamespace_1498_);
lean_ctor_set(v___x_1504_, 3, v_openDecls_1499_);
v___x_1505_ = l_Lean_Parser_mkParserState(v_docComment_1486_);
lean_dec_ref(v_docComment_1486_);
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
lean_dec(v_binders_1485_);
lean_dec(v_declName_1484_);
v___x_1513_ = lean_box(0);
v_sz_1514_ = lean_array_size(v___x_1510_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1510_, v_sz_1514_, v___x_1515_, v___x_1513_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
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
v___x_1538_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1484_, v_binders_1485_, v___x_1536_, v___x_1537_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
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
uint8_t v_suppressElabErrors_boxed_1622_; uint8_t v___x_11326__boxed_1623_; uint8_t v_res_1624_; lean_object* v_r_1625_; 
v_suppressElabErrors_boxed_1622_ = lean_unbox(v_suppressElabErrors_1619_);
v___x_11326__boxed_1623_ = lean_unbox(v___x_1620_);
v_res_1624_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1622_, v___x_11326__boxed_1623_, v_x_1621_);
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
uint8_t v_suppressElabErrors_boxed_1657_; uint8_t v___x_11390__boxed_1658_; uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_suppressElabErrors_boxed_1657_ = lean_unbox(v_suppressElabErrors_1654_);
v___x_11390__boxed_1658_ = lean_unbox(v___x_1655_);
v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1657_, v___x_11390__boxed_1658_, v_x_1656_);
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
lean_object* v_a_1677_; lean_object* v_snd_1678_; lean_object* v_toCold_1679_; lean_object* v_fst_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1737_; 
v_a_1677_ = lean_array_uget(v_as_1663_, v_i_1665_);
v_snd_1678_ = lean_ctor_get(v_a_1677_, 1);
lean_inc(v_snd_1678_);
v_toCold_1679_ = lean_ctor_get(v___y_1667_, 0);
v_fst_1680_ = lean_ctor_get(v_a_1677_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_a_1677_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v_a_1677_, 1);
lean_dec(v_unused_1738_);
v___x_1682_ = v_a_1677_;
v_isShared_1683_ = v_isSharedCheck_1737_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_fst_1680_);
lean_dec(v_a_1677_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1737_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1735_; 
v_snd_1684_ = lean_ctor_get(v_snd_1678_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_snd_1678_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_snd_1678_, 0);
lean_dec(v_unused_1736_);
v___x_1686_ = v_snd_1678_;
v_isShared_1687_ = v_isSharedCheck_1735_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_dec(v_snd_1678_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1735_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
uint8_t v_suppressElabErrors_1688_; lean_object* v_fileName_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___y_1701_; lean_object* v___y_1702_; 
v_suppressElabErrors_1688_ = lean_ctor_get_uint8(v___y_1667_, sizeof(void*)*10 + 1);
v_fileName_1689_ = lean_ctor_get(v_toCold_1679_, 0);
v___x_1690_ = lean_box(0);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_nat_dec_eq(v___x_1662_, v___x_1691_);
lean_inc_ref(v___x_1661_);
v___x_1693_ = l_Lean_FileMap_toPosition(v___x_1661_, v_fst_1680_);
lean_dec(v_fst_1680_);
v___x_1694_ = lean_box(0);
v___x_1695_ = 2;
v___x_1696_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1697_ = l_Lean_Parser_Error_toString(v_snd_1684_);
v___x_1698_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
v___x_1699_ = l_Lean_MessageData_ofFormat(v___x_1698_);
if (v_suppressElabErrors_1688_ == 0)
{
v___y_1701_ = v___y_1667_;
v___y_1702_ = v___y_1668_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___f_1733_; uint8_t v___x_1734_; 
v___x_1731_ = lean_box(v_suppressElabErrors_1688_);
v___x_1732_ = lean_box(v___x_1692_);
v___f_1733_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1733_, 0, v___x_1731_);
lean_closure_set(v___f_1733_, 1, v___x_1732_);
lean_inc_ref(v___x_1699_);
v___x_1734_ = l_Lean_MessageData_hasTag(v___f_1733_, v___x_1699_);
if (v___x_1734_ == 0)
{
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1693_);
lean_del_object(v___x_1686_);
lean_del_object(v___x_1682_);
v_a_1671_ = v___x_1690_;
goto v___jp_1670_;
}
else
{
v___y_1701_ = v___y_1667_;
v___y_1702_ = v___y_1668_;
goto v___jp_1700_;
}
}
v___jp_1700_:
{
lean_object* v___x_1703_; lean_object* v_currNamespace_1704_; lean_object* v_openDecls_1705_; lean_object* v___x_1707_; 
v___x_1703_ = lean_st_ref_take(v___y_1702_);
v_currNamespace_1704_ = lean_ctor_get(v___y_1701_, 5);
v_openDecls_1705_ = lean_ctor_get(v___y_1701_, 6);
lean_inc(v_openDecls_1705_);
lean_inc(v_currNamespace_1704_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_openDecls_1705_);
lean_ctor_set(v___x_1686_, 0, v_currNamespace_1704_);
v___x_1707_ = v___x_1686_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_currNamespace_1704_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_openDecls_1705_);
v___x_1707_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 4);
lean_ctor_set(v___x_1682_, 1, v___x_1699_);
lean_ctor_set(v___x_1682_, 0, v___x_1707_);
v___x_1709_ = v___x_1682_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1699_);
v___x_1709_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v_env_1711_; lean_object* v_nextMacroScope_1712_; lean_object* v_ngen_1713_; lean_object* v_auxDeclNGen_1714_; lean_object* v_traceState_1715_; lean_object* v_cache_1716_; lean_object* v_messages_1717_; lean_object* v_infoState_1718_; lean_object* v_snapshotTasks_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1728_; 
lean_inc_ref(v_fileName_1689_);
v___x_1710_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1710_, 0, v_fileName_1689_);
lean_ctor_set(v___x_1710_, 1, v___x_1693_);
lean_ctor_set(v___x_1710_, 2, v___x_1694_);
lean_ctor_set(v___x_1710_, 3, v___x_1696_);
lean_ctor_set(v___x_1710_, 4, v___x_1709_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*5, v___x_1692_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*5 + 1, v___x_1695_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*5 + 2, v___x_1692_);
v_env_1711_ = lean_ctor_get(v___x_1703_, 0);
v_nextMacroScope_1712_ = lean_ctor_get(v___x_1703_, 1);
v_ngen_1713_ = lean_ctor_get(v___x_1703_, 2);
v_auxDeclNGen_1714_ = lean_ctor_get(v___x_1703_, 3);
v_traceState_1715_ = lean_ctor_get(v___x_1703_, 4);
v_cache_1716_ = lean_ctor_get(v___x_1703_, 5);
v_messages_1717_ = lean_ctor_get(v___x_1703_, 6);
v_infoState_1718_ = lean_ctor_get(v___x_1703_, 7);
v_snapshotTasks_1719_ = lean_ctor_get(v___x_1703_, 8);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1721_ = v___x_1703_;
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snapshotTasks_1719_);
lean_inc(v_infoState_1718_);
lean_inc(v_messages_1717_);
lean_inc(v_cache_1716_);
lean_inc(v_traceState_1715_);
lean_inc(v_auxDeclNGen_1714_);
lean_inc(v_ngen_1713_);
lean_inc(v_nextMacroScope_1712_);
lean_inc(v_env_1711_);
lean_dec(v___x_1703_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1728_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = l_Lean_MessageLog_add(v___x_1710_, v_messages_1717_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 6, v___x_1723_);
v___x_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_env_1711_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_nextMacroScope_1712_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_ngen_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_auxDeclNGen_1714_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_traceState_1715_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v_cache_1716_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_infoState_1718_);
lean_ctor_set(v_reuseFailAlloc_1727_, 8, v_snapshotTasks_1719_);
v___x_1725_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_st_ref_put(v___y_1702_, v___x_1725_);
v_a_1671_ = v___x_1690_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1739_, lean_object* v___x_1740_, lean_object* v_as_1741_, lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
size_t v_sz_boxed_1748_; size_t v_i_boxed_1749_; lean_object* v_res_1750_; 
v_sz_boxed_1748_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1749_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1739_, v___x_1740_, v_as_1741_, v_sz_boxed_1748_, v_i_boxed_1749_, v_b_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v_as_1741_);
lean_dec(v___x_1740_);
return v_res_1750_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_box(1);
v___x_1752_ = l_Lean_MessageData_ofFormat(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1757_ = l_Lean_MessageData_ofFormat(v___x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
return v_x_1758_;
}
else
{
lean_object* v_head_1760_; lean_object* v_tail_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1783_; 
v_head_1760_ = lean_ctor_get(v_x_1759_, 0);
v_tail_1761_ = lean_ctor_get(v_x_1759_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v_x_1759_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1763_ = v_x_1759_;
v_isShared_1764_ = v_isSharedCheck_1783_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_tail_1761_);
lean_inc(v_head_1760_);
lean_dec(v_x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1783_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_before_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1781_; 
v_before_1765_ = lean_ctor_get(v_head_1760_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_head_1760_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v_head_1760_, 1);
lean_dec(v_unused_1782_);
v___x_1767_ = v_head_1760_;
v_isShared_1768_ = v_isSharedCheck_1781_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_before_1765_);
lean_dec(v_head_1760_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1781_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 7);
lean_ctor_set(v___x_1767_, 1, v___x_1769_);
lean_ctor_set(v___x_1767_, 0, v_x_1758_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_x_1758_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1764_ == 0)
{
lean_ctor_set_tag(v___x_1763_, 7);
lean_ctor_set(v___x_1763_, 1, v___x_1772_);
lean_ctor_set(v___x_1763_, 0, v___x_1771_);
v___x_1774_ = v___x_1763_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = l_Lean_MessageData_ofSyntax(v_before_1765_);
v___x_1776_ = l_Lean_indentD(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1774_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v_x_1758_ = v___x_1777_;
v_x_1759_ = v_tail_1761_;
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
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1788_ = l_Lean_MessageData_ofFormat(v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1789_, lean_object* v_macroStack_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_options_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_options_1793_ = lean_ctor_get(v___y_1791_, 1);
v___x_1794_ = l_Lean_Elab_pp_macroStack;
v___x_1795_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1793_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec(v_macroStack_1790_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_msgData_1789_);
return v___x_1796_;
}
else
{
if (lean_obj_tag(v_macroStack_1790_) == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_msgData_1789_);
return v___x_1797_;
}
else
{
lean_object* v_head_1798_; lean_object* v_after_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1814_; 
v_head_1798_ = lean_ctor_get(v_macroStack_1790_, 0);
lean_inc(v_head_1798_);
v_after_1799_ = lean_ctor_get(v_head_1798_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_head_1798_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v_head_1798_, 0);
lean_dec(v_unused_1815_);
v___x_1801_ = v_head_1798_;
v_isShared_1802_ = v_isSharedCheck_1814_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_after_1799_);
lean_dec(v_head_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1814_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 7);
lean_ctor_set(v___x_1801_, 1, v___x_1803_);
lean_ctor_set(v___x_1801_, 0, v_msgData_1789_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_msgData_1789_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_msgData_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1806_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_MessageData_ofSyntax(v_after_1799_);
v___x_1809_ = l_Lean_indentD(v___x_1808_);
v_msgData_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1810_, 0, v___x_1807_);
lean_ctor_set(v_msgData_1810_, 1, v___x_1809_);
v___x_1811_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1810_, v_macroStack_1790_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1816_, lean_object* v_macroStack_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1816_, v_macroStack_1817_, v___y_1818_);
lean_dec_ref(v___y_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v_ref_1829_; lean_object* v___x_1830_; lean_object* v_a_1831_; lean_object* v_macroStack_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1843_; 
v_ref_1829_ = lean_ctor_get(v___y_1826_, 4);
v___x_1830_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1821_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v_macroStack_1832_ = lean_ctor_get(v___y_1822_, 1);
v___x_1833_ = l_Lean_Elab_getBetterRef(v_ref_1829_, v_macroStack_1832_);
lean_inc(v_macroStack_1832_);
v___x_1834_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1831_, v_macroStack_1832_, v___y_1826_);
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1843_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1833_);
lean_ctor_set(v___x_1839_, 1, v_a_1835_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set_tag(v___x_1837_, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1839_);
v___x_1841_ = v___x_1837_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1853_, lean_object* v_msg_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_toCold_1862_; lean_object* v_options_1863_; lean_object* v_currRecDepth_1864_; lean_object* v_maxRecDepth_1865_; lean_object* v_ref_1866_; lean_object* v_currNamespace_1867_; lean_object* v_openDecls_1868_; lean_object* v_initHeartbeats_1869_; lean_object* v_maxHeartbeats_1870_; lean_object* v_currMacroScope_1871_; uint8_t v_diag_1872_; uint8_t v_suppressElabErrors_1873_; lean_object* v_ref_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_toCold_1862_ = lean_ctor_get(v___y_1859_, 0);
v_options_1863_ = lean_ctor_get(v___y_1859_, 1);
v_currRecDepth_1864_ = lean_ctor_get(v___y_1859_, 2);
v_maxRecDepth_1865_ = lean_ctor_get(v___y_1859_, 3);
v_ref_1866_ = lean_ctor_get(v___y_1859_, 4);
v_currNamespace_1867_ = lean_ctor_get(v___y_1859_, 5);
v_openDecls_1868_ = lean_ctor_get(v___y_1859_, 6);
v_initHeartbeats_1869_ = lean_ctor_get(v___y_1859_, 7);
v_maxHeartbeats_1870_ = lean_ctor_get(v___y_1859_, 8);
v_currMacroScope_1871_ = lean_ctor_get(v___y_1859_, 9);
v_diag_1872_ = lean_ctor_get_uint8(v___y_1859_, sizeof(void*)*10);
v_suppressElabErrors_1873_ = lean_ctor_get_uint8(v___y_1859_, sizeof(void*)*10 + 1);
v_ref_1874_ = l_Lean_replaceRef(v_ref_1853_, v_ref_1866_);
lean_inc(v_currMacroScope_1871_);
lean_inc(v_maxHeartbeats_1870_);
lean_inc(v_initHeartbeats_1869_);
lean_inc(v_openDecls_1868_);
lean_inc(v_currNamespace_1867_);
lean_inc(v_maxRecDepth_1865_);
lean_inc(v_currRecDepth_1864_);
lean_inc_ref(v_options_1863_);
lean_inc_ref(v_toCold_1862_);
v___x_1875_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1875_, 0, v_toCold_1862_);
lean_ctor_set(v___x_1875_, 1, v_options_1863_);
lean_ctor_set(v___x_1875_, 2, v_currRecDepth_1864_);
lean_ctor_set(v___x_1875_, 3, v_maxRecDepth_1865_);
lean_ctor_set(v___x_1875_, 4, v_ref_1874_);
lean_ctor_set(v___x_1875_, 5, v_currNamespace_1867_);
lean_ctor_set(v___x_1875_, 6, v_openDecls_1868_);
lean_ctor_set(v___x_1875_, 7, v_initHeartbeats_1869_);
lean_ctor_set(v___x_1875_, 8, v_maxHeartbeats_1870_);
lean_ctor_set(v___x_1875_, 9, v_currMacroScope_1871_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*10, v_diag_1872_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*10 + 1, v_suppressElabErrors_1873_);
v___x_1876_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___x_1875_, v___y_1860_);
lean_dec_ref_known(v___x_1875_, 10);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1877_, v_msg_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v_ref_1877_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; uint8_t v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; uint8_t v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; uint8_t v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
lean_inc(v_docComment_1887_);
v___x_2046_ = l_Lean_Syntax_getKind(v_docComment_1887_);
v___x_2047_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2048_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2049_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2050_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2051_ = lean_name_eq(v___x_2046_, v___x_2050_);
lean_dec(v___x_2046_);
if (v___x_2051_ == 0)
{
goto v___jp_2022_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = l_Lean_Syntax_getArg(v_docComment_1887_, v___x_2052_);
if (lean_obj_tag(v___x_2053_) == 1)
{
lean_object* v_kind_2054_; 
v_kind_2054_ = lean_ctor_get(v___x_2053_, 1);
lean_inc(v_kind_2054_);
if (lean_obj_tag(v_kind_2054_) == 1)
{
lean_object* v_pre_2055_; 
v_pre_2055_ = lean_ctor_get(v_kind_2054_, 0);
lean_inc(v_pre_2055_);
if (lean_obj_tag(v_pre_2055_) == 1)
{
lean_object* v_pre_2056_; 
v_pre_2056_ = lean_ctor_get(v_pre_2055_, 0);
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
if (lean_obj_tag(v_pre_2058_) == 0)
{
lean_object* v_info_2059_; lean_object* v_args_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2084_; 
v_info_2059_ = lean_ctor_get(v___x_2053_, 0);
v_args_2060_ = lean_ctor_get(v___x_2053_, 2);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2053_, 1);
lean_dec(v_unused_2085_);
v___x_2062_ = v___x_2053_;
v_isShared_2063_ = v_isSharedCheck_2084_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_args_2060_);
lean_inc(v_info_2059_);
lean_dec(v___x_2053_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2084_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_str_2064_; lean_object* v_str_2065_; lean_object* v_str_2066_; lean_object* v_str_2067_; uint8_t v___x_2068_; 
v_str_2064_ = lean_ctor_get(v_kind_2054_, 1);
lean_inc_ref(v_str_2064_);
lean_dec_ref_known(v_kind_2054_, 2);
v_str_2065_ = lean_ctor_get(v_pre_2055_, 1);
lean_inc_ref(v_str_2065_);
lean_dec_ref_known(v_pre_2055_, 2);
v_str_2066_ = lean_ctor_get(v_pre_2056_, 1);
lean_inc_ref(v_str_2066_);
lean_dec_ref_known(v_pre_2056_, 2);
v_str_2067_ = lean_ctor_get(v_pre_2057_, 1);
lean_inc_ref(v_str_2067_);
lean_dec_ref_known(v_pre_2057_, 2);
v___x_2068_ = lean_string_dec_eq(v_str_2067_, v___x_2047_);
lean_dec_ref(v_str_2067_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v_str_2066_);
lean_dec_ref(v_str_2065_);
lean_dec_ref(v_str_2064_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_args_2060_);
lean_dec(v_info_2059_);
goto v___jp_2022_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_string_dec_eq(v_str_2066_, v___x_2048_);
lean_dec_ref(v_str_2066_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_str_2065_);
lean_dec_ref(v_str_2064_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_args_2060_);
lean_dec(v_info_2059_);
goto v___jp_2022_;
}
else
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_string_dec_eq(v_str_2065_, v___x_2049_);
lean_dec_ref(v_str_2065_);
if (v___x_2070_ == 0)
{
lean_dec_ref(v_str_2064_);
lean_del_object(v___x_2062_);
lean_dec_ref(v_args_2060_);
lean_dec(v_info_2059_);
goto v___jp_2022_;
}
else
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2072_ = lean_string_dec_eq(v_str_2064_, v___x_2071_);
lean_dec_ref(v_str_2064_);
if (v___x_2072_ == 0)
{
lean_del_object(v___x_2062_);
lean_dec_ref(v_args_2060_);
lean_dec(v_info_2059_);
goto v___jp_2022_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec(v_docComment_1887_);
v___x_2073_ = l_Lean_Name_str___override(v_pre_2058_, v___x_2047_);
v___x_2074_ = l_Lean_Name_str___override(v___x_2073_, v___x_2048_);
v___x_2075_ = l_Lean_Name_str___override(v___x_2074_, v___x_2049_);
v___x_2076_ = l_Lean_Name_str___override(v___x_2075_, v___x_2071_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2076_);
v___x_2078_ = v___x_2062_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_info_2059_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_args_2060_);
v___x_2078_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = l_Lean_Syntax_getArg(v___x_2078_, v___x_2079_);
lean_dec_ref(v___x_2078_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
}
}
}
}
}
}
else
{
lean_dec(v_pre_2058_);
lean_dec_ref_known(v_pre_2057_, 2);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2053_, 3);
goto v___jp_2022_;
}
}
else
{
lean_dec(v_pre_2057_);
lean_dec_ref_known(v_pre_2056_, 2);
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2053_, 3);
goto v___jp_2022_;
}
}
else
{
lean_dec_ref_known(v_pre_2055_, 2);
lean_dec(v_pre_2056_);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2053_, 3);
goto v___jp_2022_;
}
}
else
{
lean_dec(v_pre_2055_);
lean_dec_ref_known(v_kind_2054_, 2);
lean_dec_ref_known(v___x_2053_, 3);
goto v___jp_2022_;
}
}
else
{
lean_dec_ref_known(v___x_2053_, 3);
lean_dec(v_kind_2054_);
goto v___jp_2022_;
}
}
else
{
lean_dec(v___x_2053_);
goto v___jp_2022_;
}
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1908_; lean_object* v_currNamespace_1909_; lean_object* v_openDecls_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_env_1914_; lean_object* v_nextMacroScope_1915_; lean_object* v_ngen_1916_; lean_object* v_auxDeclNGen_1917_; lean_object* v_traceState_1918_; lean_object* v_cache_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1931_; 
v___x_1908_ = lean_st_ref_take(v___y_1907_);
v_currNamespace_1909_ = lean_ctor_get(v___y_1906_, 5);
v_openDecls_1910_ = lean_ctor_get(v___y_1906_, 6);
lean_inc(v_openDecls_1910_);
lean_inc(v_currNamespace_1909_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_currNamespace_1909_);
lean_ctor_set(v___x_1911_, 1, v_openDecls_1910_);
v___x_1912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___y_1901_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1903_);
v___x_1913_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1913_, 0, v___y_1903_);
lean_ctor_set(v___x_1913_, 1, v___y_1904_);
lean_ctor_set(v___x_1913_, 2, v___y_1900_);
lean_ctor_set(v___x_1913_, 3, v___y_1902_);
lean_ctor_set(v___x_1913_, 4, v___x_1912_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*5, v___y_1899_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*5 + 1, v___y_1905_);
lean_ctor_set_uint8(v___x_1913_, sizeof(void*)*5 + 2, v___y_1899_);
v_env_1914_ = lean_ctor_get(v___x_1908_, 0);
v_nextMacroScope_1915_ = lean_ctor_get(v___x_1908_, 1);
v_ngen_1916_ = lean_ctor_get(v___x_1908_, 2);
v_auxDeclNGen_1917_ = lean_ctor_get(v___x_1908_, 3);
v_traceState_1918_ = lean_ctor_get(v___x_1908_, 4);
v_cache_1919_ = lean_ctor_get(v___x_1908_, 5);
v_messages_1920_ = lean_ctor_get(v___x_1908_, 6);
v_infoState_1921_ = lean_ctor_get(v___x_1908_, 7);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1908_, 8);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1924_ = v___x_1908_;
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_cache_1919_);
lean_inc(v_traceState_1918_);
lean_inc(v_auxDeclNGen_1917_);
lean_inc(v_ngen_1916_);
lean_inc(v_nextMacroScope_1915_);
lean_inc(v_env_1914_);
lean_dec(v___x_1908_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = l_Lean_MessageLog_add(v___x_1913_, v_messages_1920_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 6, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_env_1914_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_nextMacroScope_1915_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_ngen_1916_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_auxDeclNGen_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_traceState_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 5, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1930_, 6, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1930_, 7, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_1930_, 8, v_snapshotTasks_1922_);
v___x_1928_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_st_ref_put(v___y_1907_, v___x_1928_);
goto v___jp_1895_;
}
}
}
v___jp_1932_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_inc_ref(v___y_1939_);
v___x_1940_ = l_Lean_Parser_ParserState_allErrors(v___y_1939_);
v___x_1941_ = lean_array_get_size(v___x_1940_);
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_nat_dec_eq(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; size_t v_sz_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
lean_dec_ref(v___y_1939_);
lean_dec_ref(v___y_1935_);
v___x_1944_ = lean_box(0);
v_sz_1945_ = lean_array_size(v___x_1940_);
v___x_1946_ = ((size_t)0ULL);
lean_inc_ref(v___y_1934_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1934_, v___x_1941_, v___x_1940_, v_sz_1945_, v___x_1946_, v___x_1944_, v___y_1892_, v___y_1893_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1955_; 
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1955_ == 0)
{
lean_object* v_unused_1956_; 
v_unused_1956_ = lean_ctor_get(v___x_1947_, 0);
lean_dec(v_unused_1956_);
v___x_1949_ = v___x_1947_;
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v___x_1947_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1955_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1951_ = lean_box(0);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1951_);
v___x_1953_ = v___x_1949_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_a_1957_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1947_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1947_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_stxStack_1965_; lean_object* v_pos_1966_; uint8_t v___x_1967_; 
lean_dec_ref(v___x_1940_);
v_stxStack_1965_ = lean_ctor_get(v___y_1939_, 0);
lean_inc_ref(v_stxStack_1965_);
v_pos_1966_ = lean_ctor_get(v___y_1939_, 2);
lean_inc(v_pos_1966_);
lean_dec_ref(v___y_1939_);
v___x_1967_ = l_Lean_Parser_InputContext_atEnd(v___y_1935_, v_pos_1966_);
lean_dec_ref(v___y_1935_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint32_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_stxStack_1965_);
lean_inc_ref(v___y_1934_);
v___x_1968_ = l_Lean_FileMap_toPosition(v___y_1934_, v_pos_1966_);
v___x_1969_ = lean_box(0);
v___x_1970_ = 2;
v___x_1971_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1972_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1973_ = lean_string_utf8_get(v___y_1937_, v_pos_1966_);
lean_dec(v_pos_1966_);
v___x_1974_ = lean_string_push(v___x_1971_, v___x_1973_);
v___x_1975_ = lean_string_append(v___x_1972_, v___x_1974_);
lean_dec_ref(v___x_1974_);
v___x_1976_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1977_ = lean_string_append(v___x_1975_, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
v___x_1979_ = l_Lean_MessageData_ofFormat(v___x_1978_);
if (v___y_1936_ == 0)
{
v___y_1899_ = v___x_1967_;
v___y_1900_ = v___x_1969_;
v___y_1901_ = v___x_1979_;
v___y_1902_ = v___x_1971_;
v___y_1903_ = v___y_1938_;
v___y_1904_ = v___x_1968_;
v___y_1905_ = v___x_1970_;
v___y_1906_ = v___y_1892_;
v___y_1907_ = v___y_1893_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___f_1982_; uint8_t v___x_1983_; 
v___x_1980_ = lean_box(v___y_1933_);
v___x_1981_ = lean_box(v___x_1967_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1982_, 0, v___x_1980_);
lean_closure_set(v___f_1982_, 1, v___x_1981_);
lean_inc_ref(v___x_1979_);
v___x_1983_ = l_Lean_MessageData_hasTag(v___f_1982_, v___x_1979_);
if (v___x_1983_ == 0)
{
lean_dec_ref(v___x_1979_);
lean_dec_ref(v___x_1968_);
goto v___jp_1895_;
}
else
{
v___y_1899_ = v___x_1967_;
v___y_1900_ = v___x_1969_;
v___y_1901_ = v___x_1979_;
v___y_1902_ = v___x_1971_;
v___y_1903_ = v___y_1938_;
v___y_1904_ = v___x_1968_;
v___y_1905_ = v___x_1970_;
v___y_1906_ = v___y_1892_;
v___y_1907_ = v___y_1893_;
goto v___jp_1898_;
}
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec(v_pos_1966_);
v___x_1984_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1965_);
lean_dec_ref(v_stxStack_1965_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
}
v___jp_1987_:
{
lean_object* v___x_1999_; lean_object* v_env_2000_; lean_object* v_ictx_2001_; lean_object* v_pmctx_2002_; lean_object* v_blockCtxt_2003_; lean_object* v___x_2004_; lean_object* v_s_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_s_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_1999_ = lean_st_ref_get(v___y_1893_);
v_env_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref_n(v_env_2000_, 2);
lean_dec(v___x_1999_);
lean_inc(v___y_1998_);
lean_inc_ref_n(v___y_1992_, 2);
lean_inc_ref(v___y_1995_);
lean_inc_ref(v___y_1989_);
v_ictx_2001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2001_, 0, v___y_1989_);
lean_ctor_set(v_ictx_2001_, 1, v___y_1995_);
lean_ctor_set(v_ictx_2001_, 2, v___y_1992_);
lean_ctor_set(v_ictx_2001_, 3, v___y_1998_);
lean_inc(v___y_1996_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1997_);
v_pmctx_2002_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2002_, 0, v_env_2000_);
lean_ctor_set(v_pmctx_2002_, 1, v___y_1997_);
lean_ctor_set(v_pmctx_2002_, 2, v___y_1994_);
lean_ctor_set(v_pmctx_2002_, 3, v___y_1996_);
lean_inc(v___y_1991_);
v_blockCtxt_2003_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_1992_, v___y_1991_, v___y_1998_);
v___x_2004_ = l_Lean_Parser_mkParserState(v___y_1989_);
lean_inc_ref(v___x_2004_);
v_s_2005_ = l_Lean_Parser_ParserState_setPos(v___x_2004_, v___y_1991_);
v___x_2006_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_2006_, 0, v_blockCtxt_2003_);
v___x_2007_ = l_Lean_Parser_getTokenTable(v_env_2000_);
lean_inc_ref(v___x_2007_);
lean_inc_ref(v_pmctx_2002_);
lean_inc_ref(v_ictx_2001_);
v_s_2008_ = l_Lean_Parser_ParserFn_run(v___x_2006_, v_ictx_2001_, v_pmctx_2002_, v___x_2007_, v_s_2005_);
lean_inc_ref(v_s_2008_);
v___x_2009_ = l_Lean_Parser_ParserState_allErrors(v_s_2008_);
v___x_2010_ = lean_array_get_size(v___x_2009_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_nat_dec_eq(v___x_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_dec_ref(v___x_2007_);
lean_dec_ref(v___x_2004_);
lean_dec_ref_known(v_pmctx_2002_, 4);
lean_dec(v___y_1990_);
v___y_1933_ = v___y_1988_;
v___y_1934_ = v___y_1992_;
v___y_1935_ = v_ictx_2001_;
v___y_1936_ = v___y_1993_;
v___y_1937_ = v___y_1989_;
v___y_1938_ = v___y_1995_;
v___y_1939_ = v_s_2008_;
goto v___jp_1932_;
}
else
{
lean_object* v_pos_2013_; uint8_t v___x_2014_; 
v_pos_2013_ = lean_ctor_get(v_s_2008_, 2);
lean_inc(v_pos_2013_);
v___x_2014_ = l_Lean_Parser_InputContext_atEnd(v_ictx_2001_, v_pos_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_dec_ref(v_s_2008_);
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_1990_);
lean_ctor_set(v___x_2017_, 1, v___x_2011_);
v___x_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2011_);
lean_ctor_set(v___x_2018_, 1, v___x_2015_);
lean_ctor_set(v___x_2018_, 2, v___x_2016_);
lean_ctor_set(v___x_2018_, 3, v___x_2017_);
lean_ctor_set(v___x_2018_, 4, v___x_2011_);
v___x_2019_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = l_Lean_Parser_ParserState_setPos(v___x_2004_, v_pos_2013_);
lean_inc_ref(v_ictx_2001_);
v___x_2021_ = l_Lean_Parser_ParserFn_run(v___x_2019_, v_ictx_2001_, v_pmctx_2002_, v___x_2007_, v___x_2020_);
v___y_1933_ = v___y_1988_;
v___y_1934_ = v___y_1992_;
v___y_1935_ = v_ictx_2001_;
v___y_1936_ = v___y_1993_;
v___y_1937_ = v___y_1989_;
v___y_1938_ = v___y_1995_;
v___y_1939_ = v___x_2021_;
goto v___jp_1932_;
}
else
{
lean_dec(v_pos_2013_);
lean_dec_ref(v___x_2007_);
lean_dec_ref(v___x_2004_);
lean_dec_ref_known(v_pmctx_2002_, 4);
lean_dec(v___y_1990_);
v___y_1933_ = v___y_1988_;
v___y_1934_ = v___y_1992_;
v___y_1935_ = v_ictx_2001_;
v___y_1936_ = v___y_1993_;
v___y_1937_ = v___y_1989_;
v___y_1938_ = v___y_1995_;
v___y_1939_ = v_s_2008_;
goto v___jp_1932_;
}
}
}
v___jp_2022_:
{
lean_object* v_toCold_2023_; lean_object* v_options_2024_; lean_object* v_currNamespace_2025_; lean_object* v_openDecls_2026_; uint8_t v_suppressElabErrors_2027_; lean_object* v_fileName_2028_; lean_object* v_fileMap_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; lean_object* v___x_2033_; 
v_toCold_2023_ = lean_ctor_get(v___y_1892_, 0);
v_options_2024_ = lean_ctor_get(v___y_1892_, 1);
v_currNamespace_2025_ = lean_ctor_get(v___y_1892_, 5);
v_openDecls_2026_ = lean_ctor_get(v___y_1892_, 6);
v_suppressElabErrors_2027_ = lean_ctor_get_uint8(v___y_1892_, sizeof(void*)*10 + 1);
v_fileName_2028_ = lean_ctor_get(v_toCold_2023_, 0);
v_fileMap_2029_ = lean_ctor_get(v_toCold_2023_, 1);
v___x_2030_ = lean_unsigned_to_nat(1u);
v___x_2031_ = l_Lean_Syntax_getArg(v_docComment_1887_, v___x_2030_);
v___x_2032_ = 1;
v___x_2033_ = l_Lean_Syntax_getPos_x3f(v___x_2031_, v___x_2032_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2035_; 
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = l_Lean_Syntax_getTailPos_x3f(v___x_2031_, v___x_2032_);
lean_dec(v___x_2031_);
if (lean_obj_tag(v___x_2035_) == 1)
{
lean_object* v_val_2036_; lean_object* v_source_2037_; lean_object* v___x_2038_; lean_object* v_endPos_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
lean_dec(v_docComment_1887_);
v_val_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v_source_2037_ = lean_ctor_get(v_fileMap_2029_, 0);
v___x_2038_ = lean_string_utf8_prev(v_source_2037_, v_val_2036_);
lean_dec(v_val_2036_);
v_endPos_2039_ = lean_string_utf8_prev(v_source_2037_, v___x_2038_);
lean_dec(v___x_2038_);
v___x_2040_ = lean_string_utf8_byte_size(v_source_2037_);
v___x_2041_ = lean_nat_dec_le(v_endPos_2039_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_dec(v_endPos_2039_);
v___y_1988_ = v_suppressElabErrors_2027_;
v___y_1989_ = v_source_2037_;
v___y_1990_ = v___x_2030_;
v___y_1991_ = v_val_2034_;
v___y_1992_ = v_fileMap_2029_;
v___y_1993_ = v_suppressElabErrors_2027_;
v___y_1994_ = v_currNamespace_2025_;
v___y_1995_ = v_fileName_2028_;
v___y_1996_ = v_openDecls_2026_;
v___y_1997_ = v_options_2024_;
v___y_1998_ = v___x_2040_;
goto v___jp_1987_;
}
else
{
v___y_1988_ = v_suppressElabErrors_2027_;
v___y_1989_ = v_source_2037_;
v___y_1990_ = v___x_2030_;
v___y_1991_ = v_val_2034_;
v___y_1992_ = v_fileMap_2029_;
v___y_1993_ = v_suppressElabErrors_2027_;
v___y_1994_ = v_currNamespace_2025_;
v___y_1995_ = v_fileName_2028_;
v___y_1996_ = v_openDecls_2026_;
v___y_1997_ = v_options_2024_;
v___y_1998_ = v_endPos_2039_;
goto v___jp_1987_;
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec(v___x_2035_);
lean_dec(v_val_2034_);
v___x_2042_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2043_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1887_, v___x_2042_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v_docComment_1887_);
return v___x_2043_;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v___x_2033_);
lean_dec(v___x_2031_);
v___x_2044_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2045_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1887_, v___x_2044_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v_docComment_1887_);
return v___x_2045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2108_, lean_object* v_binders_2109_, lean_object* v_docComment_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v_body_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2118_ = lean_unsigned_to_nat(1u);
v_body_2119_ = l_Lean_Syntax_getArg(v_docComment_2110_, v___x_2118_);
v___x_2120_ = 1;
v___x_2121_ = l_Lean_Syntax_getPos_x3f(v_body_2119_, v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2119_);
v___x_2123_ = l_Lean_Syntax_isOfKind(v_body_2119_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v_body_2119_);
v___x_2124_ = l_Lean_TSyntax_getDocString(v_docComment_2110_);
lean_dec(v_docComment_2110_);
v___x_2125_ = l_Lean_versoDocStringOfText(v_declName_2108_, v_binders_2109_, v___x_2124_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
lean_dec(v_docComment_2110_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l_Lean_Syntax_getArg(v_body_2119_, v___x_2126_);
lean_dec(v_body_2119_);
v___x_2128_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2127_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2130_ = l_Lean_Syntax_getArgs(v___x_2127_);
lean_dec(v___x_2127_);
v___x_2131_ = lean_box(0);
v___x_2132_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2108_, v_binders_2109_, v___x_2130_, v___x_2131_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = l_Lean_Syntax_getArg(v___x_2127_, v___x_2126_);
lean_dec(v___x_2127_);
v___x_2134_ = l_Lean_Syntax_getAtomVal(v___x_2133_);
lean_dec(v___x_2133_);
v___x_2135_ = l_Lean_versoDocStringOfText(v_declName_2108_, v_binders_2109_, v___x_2134_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2135_;
}
}
}
else
{
lean_object* v___x_2136_; 
lean_dec_ref_known(v___x_2121_, 1);
lean_dec(v_body_2119_);
v___x_2136_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2187_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2187_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2187_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
if (lean_obj_tag(v_a_2137_) == 1)
{
lean_object* v_val_2141_; lean_object* v___x_2142_; size_t v_sz_2143_; size_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; 
lean_del_object(v___x_2139_);
v_val_2141_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v_a_2137_, 1);
v___x_2142_ = l_Lean_Syntax_getArgs(v_val_2141_);
lean_dec(v_val_2141_);
v_sz_2143_ = lean_array_size(v___x_2142_);
v___x_2144_ = ((size_t)0ULL);
v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2143_, v___x_2144_, v___x_2142_);
v___x_2146_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2146_, 0, v___x_2145_);
v___x_2147_ = 0;
v___x_2148_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2108_, v_binders_2109_, v___x_2146_, v___x_2147_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2174_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2174_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2174_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_fst_2153_; lean_object* v_snd_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2173_; 
v_fst_2153_ = lean_ctor_get(v_a_2149_, 0);
v_snd_2154_ = lean_ctor_get(v_a_2149_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2156_ = v_a_2149_;
v_isShared_2157_ = v_isSharedCheck_2173_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_snd_2154_);
lean_inc(v_fst_2153_);
lean_dec(v_a_2149_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2173_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_fst_2158_; lean_object* v_snd_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2172_; 
v_fst_2158_ = lean_ctor_get(v_fst_2153_, 0);
v_snd_2159_ = lean_ctor_get(v_fst_2153_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_fst_2153_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2161_ = v_fst_2153_;
v_isShared_2162_ = v_isSharedCheck_2172_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_snd_2159_);
lean_inc(v_fst_2158_);
lean_dec(v_fst_2153_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2172_;
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
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_fst_2158_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2159_);
v___x_2164_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2166_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2164_);
v___x_2166_ = v___x_2156_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_snd_2154_);
v___x_2166_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2168_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2166_);
v___x_2168_ = v___x_2151_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_a_2175_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2148_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2148_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec(v_a_2137_);
lean_dec(v_binders_2109_);
lean_dec(v_declName_2108_);
v___x_2183_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2183_);
v___x_2185_ = v___x_2139_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_binders_2109_);
lean_dec(v_declName_2108_);
v_a_2188_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2136_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2136_);
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
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2196_, lean_object* v_binders_2197_, lean_object* v_docComment_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_versoDocString(v_declName_2196_, v_binders_2197_, v_docComment_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2207_, lean_object* v___x_2208_, lean_object* v_as_2209_, size_t v_sz_2210_, size_t v_i_2211_, lean_object* v_b_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2207_, v___x_2208_, v_as_2209_, v_sz_2210_, v_i_2211_, v_b_2212_, v___y_2217_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v_as_2223_, lean_object* v_sz_2224_, lean_object* v_i_2225_, lean_object* v_b_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
size_t v_sz_boxed_2234_; size_t v_i_boxed_2235_; lean_object* v_res_2236_; 
v_sz_boxed_2234_ = lean_unbox_usize(v_sz_2224_);
lean_dec(v_sz_2224_);
v_i_boxed_2235_ = lean_unbox_usize(v_i_2225_);
lean_dec(v_i_2225_);
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2221_, v___x_2222_, v_as_2223_, v_sz_boxed_2234_, v_i_boxed_2235_, v_b_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v_as_2223_);
lean_dec(v___x_2222_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2237_, lean_object* v_ref_2238_, lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2238_, v_msg_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_ref_2249_, lean_object* v_msg_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2248_, v_ref_2249_, v_msg_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v_ref_2249_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2259_, lean_object* v_msg_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2269_, v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2279_, lean_object* v_macroStack_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2279_, v_macroStack_2280_, v___y_2285_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2289_, lean_object* v_macroStack_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2289_, v_macroStack_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2299_, lean_object* v_doc_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2316_; lean_object* v_env_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2308_ = lean_st_ref_get(v_a_2306_);
v_env_2323_ = lean_ctor_get(v___x_2308_, 0);
lean_inc_ref(v_env_2323_);
lean_dec(v___x_2308_);
v___x_2324_ = l_Lean_getMainVersoModuleDocs(v_env_2323_);
v___x_2325_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2324_);
lean_dec_ref(v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
v___y_2316_ = v___x_2325_;
goto v___jp_2315_;
}
else
{
lean_object* v_val_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
v_val_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_val_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_val_2326_, v___x_2330_);
lean_dec(v_val_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
v___y_2316_ = v___x_2333_;
goto v___jp_2315_;
}
}
}
v___jp_2309_:
{
lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2312_, 0, v_range_2299_);
lean_closure_set(v___x_2312_, 1, v___y_2310_);
lean_closure_set(v___x_2312_, 2, v___y_2311_);
v___x_2313_ = 0;
v___x_2314_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2312_, v___x_2313_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2314_;
}
v___jp_2315_:
{
lean_object* v___x_2317_; size_t v_sz_2318_; size_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = l_Lean_Syntax_getArgs(v_doc_2300_);
v_sz_2318_ = lean_array_size(v___x_2317_);
v___x_2319_ = ((size_t)0ULL);
v___x_2320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2318_, v___x_2319_, v___x_2317_);
if (lean_obj_tag(v___y_2316_) == 0)
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___y_2310_ = v___x_2320_;
v___y_2311_ = v___x_2321_;
goto v___jp_2309_;
}
else
{
lean_object* v_val_2322_; 
v_val_2322_ = lean_ctor_get(v___y_2316_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v___y_2316_, 1);
v___y_2310_ = v___x_2320_;
v___y_2311_ = v_val_2322_;
goto v___jp_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2336_, lean_object* v_doc_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_versoModDocString(v_range_2336_, v_doc_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_doc_2337_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2355_, lean_object* v_docComment_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2365_ = l_Lean_versoDocStringOfText(v_declName_2355_, v___x_2364_, v_docComment_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2366_, lean_object* v_docComment_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_versoDocStringFromString(v_declName_2366_, v_docComment_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_a_2368_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2376_, lean_object* v_declName_2377_, lean_object* v_env_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = l_Lean_docStringExt;
v___x_2380_ = l_String_removeLeadingSpaces(v_docString_2376_);
v___x_2381_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2379_, v_env_2378_, v_declName_2377_, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2382_, lean_object* v_modifyEnv_2383_, lean_object* v_docString_2384_){
_start:
{
lean_object* v___f_2385_; lean_object* v___x_2386_; 
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2385_, 0, v_docString_2384_);
lean_closure_set(v___f_2385_, 1, v_declName_2382_);
v___x_2386_ = lean_apply_1(v_modifyEnv_2383_, v___f_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2387_, lean_object* v_inst_2388_, lean_object* v_docComment_2389_, lean_object* v_toBind_2390_, lean_object* v___f_2391_, lean_object* v_____r_2392_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = l_Lean_getDocStringText___redArg(v_inst_2387_, v_inst_2388_, v_docComment_2389_);
v___x_2394_ = lean_apply_4(v_toBind_2390_, lean_box(0), lean_box(0), v___x_2393_, v___f_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_inst_2399_, lean_object* v_docComment_2400_, lean_object* v_toBind_2401_, lean_object* v___f_2402_, lean_object* v_____r_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = l_Lean_validateDocComment___redArg(v_inst_2395_, v_inst_2396_, v_inst_2397_, v_inst_2398_, v_inst_2399_, v_docComment_2400_);
v___x_2405_ = lean_apply_4(v_toBind_2401_, lean_box(0), lean_box(0), v___x_2404_, v___f_2402_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_docComment_2411_, lean_object* v_toBind_2412_, lean_object* v___f_2413_, lean_object* v_____r_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2406_, v_inst_2407_, v_inst_2408_, v_inst_2409_, v_inst_2410_, v_docComment_2411_, v_toBind_2412_, v___f_2413_, v_____r_2414_);
lean_dec(v_docComment_2411_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2416_, lean_object* v_____r_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_apply_1(v___f_2416_, v_____r_2417_);
return v___x_2418_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2421_ = l_Lean_stringToMessageData(v___x_2420_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2425_, lean_object* v_declName_2426_, uint8_t v___x_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_toBind_2430_, lean_object* v___f_2431_, lean_object* v_____do__lift_2432_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2432_, v_declName_2426_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_dec(v___f_2431_);
lean_dec(v_toBind_2430_);
lean_dec_ref(v_inst_2429_);
lean_dec_ref(v_inst_2428_);
lean_dec(v_declName_2426_);
goto v___jp_2433_;
}
else
{
lean_dec_ref_known(v___x_2436_, 1);
if (v___x_2427_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_dec(v___f_2425_);
v___x_2437_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2438_ = l_Lean_MessageData_ofConstName(v_declName_2426_, v___x_2427_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2439_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = l_Lean_throwError___redArg(v_inst_2428_, v_inst_2429_, v___x_2441_);
v___x_2443_ = lean_apply_4(v_toBind_2430_, lean_box(0), lean_box(0), v___x_2442_, v___f_2431_);
return v___x_2443_;
}
else
{
lean_dec(v___f_2431_);
lean_dec(v_toBind_2430_);
lean_dec_ref(v_inst_2429_);
lean_dec_ref(v_inst_2428_);
lean_dec(v_declName_2426_);
goto v___jp_2433_;
}
}
v___jp_2433_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_apply_1(v___f_2425_, v___x_2434_);
return v___x_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2444_, lean_object* v_declName_2445_, lean_object* v___x_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_toBind_2449_, lean_object* v___f_2450_, lean_object* v_____do__lift_2451_){
_start:
{
uint8_t v___x_243__boxed_2452_; lean_object* v_res_2453_; 
v___x_243__boxed_2452_ = lean_unbox(v___x_2446_);
v_res_2453_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2444_, v_declName_2445_, v___x_243__boxed_2452_, v_inst_2447_, v_inst_2448_, v_toBind_2449_, v___f_2450_, v_____do__lift_2451_);
lean_dec_ref(v_____do__lift_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_declName_2461_, lean_object* v_docComment_2462_){
_start:
{
lean_object* v_toApplicative_2463_; lean_object* v_toBind_2464_; lean_object* v_toPure_2465_; uint8_t v___x_2466_; 
v_toApplicative_2463_ = lean_ctor_get(v_inst_2454_, 0);
v_toBind_2464_ = lean_ctor_get(v_inst_2454_, 1);
lean_inc(v_toBind_2464_);
v_toPure_2465_ = lean_ctor_get(v_toApplicative_2463_, 1);
v___x_2466_ = l_Lean_Name_isAnonymous(v_declName_2461_);
if (v___x_2466_ == 0)
{
lean_object* v_getEnv_2467_; lean_object* v_modifyEnv_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___f_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; 
v_getEnv_2467_ = lean_ctor_get(v_inst_2457_, 0);
lean_inc(v_getEnv_2467_);
v_modifyEnv_2468_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc(v_modifyEnv_2468_);
lean_dec_ref(v_inst_2457_);
lean_inc(v_declName_2461_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2469_, 0, v_declName_2461_);
lean_closure_set(v___f_2469_, 1, v_modifyEnv_2468_);
lean_inc_n(v_toBind_2464_, 3);
lean_inc(v_docComment_2462_);
lean_inc_ref(v_inst_2458_);
lean_inc_ref_n(v_inst_2454_, 2);
v___f_2470_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2470_, 0, v_inst_2454_);
lean_closure_set(v___f_2470_, 1, v_inst_2458_);
lean_closure_set(v___f_2470_, 2, v_docComment_2462_);
lean_closure_set(v___f_2470_, 3, v_toBind_2464_);
lean_closure_set(v___f_2470_, 4, v___f_2469_);
v___f_2471_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2471_, 0, v_inst_2454_);
lean_closure_set(v___f_2471_, 1, v_inst_2455_);
lean_closure_set(v___f_2471_, 2, v_inst_2459_);
lean_closure_set(v___f_2471_, 3, v_inst_2460_);
lean_closure_set(v___f_2471_, 4, v_inst_2456_);
lean_closure_set(v___f_2471_, 5, v_docComment_2462_);
lean_closure_set(v___f_2471_, 6, v_toBind_2464_);
lean_closure_set(v___f_2471_, 7, v___f_2470_);
lean_inc_ref(v___f_2471_);
v___f_2472_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2472_, 0, v___f_2471_);
v___x_2473_ = lean_box(v___x_2466_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2474_, 0, v___f_2471_);
lean_closure_set(v___f_2474_, 1, v_declName_2461_);
lean_closure_set(v___f_2474_, 2, v___x_2473_);
lean_closure_set(v___f_2474_, 3, v_inst_2454_);
lean_closure_set(v___f_2474_, 4, v_inst_2458_);
lean_closure_set(v___f_2474_, 5, v_toBind_2464_);
lean_closure_set(v___f_2474_, 6, v___f_2472_);
v___x_2475_ = lean_apply_4(v_toBind_2464_, lean_box(0), lean_box(0), v_getEnv_2467_, v___f_2474_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc(v_toPure_2465_);
lean_dec(v_toBind_2464_);
lean_dec(v_docComment_2462_);
lean_dec(v_declName_2461_);
lean_dec(v_inst_2460_);
lean_dec_ref(v_inst_2459_);
lean_dec_ref(v_inst_2458_);
lean_dec_ref(v_inst_2457_);
lean_dec(v_inst_2456_);
lean_dec(v_inst_2455_);
lean_dec_ref(v_inst_2454_);
v___x_2476_ = lean_box(0);
v___x_2477_ = lean_apply_2(v_toPure_2465_, lean_box(0), v___x_2476_);
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_declName_2486_, lean_object* v_docComment_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_addMarkdownDocString___redArg(v_inst_2479_, v_inst_2480_, v_inst_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_declName_2486_, v_docComment_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2489_, lean_object* v_x1_2490_, lean_object* v_x2_2491_){
_start:
{
lean_object* v_index_2492_; lean_object* v_sourceString_2493_; lean_object* v_imports_2494_; lean_object* v_currNamespace_2495_; lean_object* v_openDecls_2496_; lean_object* v_options_2497_; lean_object* v_check_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2511_; 
v_index_2492_ = lean_ctor_get(v_x2_2491_, 1);
v_sourceString_2493_ = lean_ctor_get(v_x2_2491_, 2);
v_imports_2494_ = lean_ctor_get(v_x2_2491_, 3);
v_currNamespace_2495_ = lean_ctor_get(v_x2_2491_, 4);
v_openDecls_2496_ = lean_ctor_get(v_x2_2491_, 5);
v_options_2497_ = lean_ctor_get(v_x2_2491_, 6);
v_check_2498_ = lean_ctor_get(v_x2_2491_, 7);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_x2_2491_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v_x2_2491_, 0);
lean_dec(v_unused_2512_);
v___x_2500_ = v_x2_2491_;
v_isShared_2501_ = v_isSharedCheck_2511_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_check_2498_);
lean_inc(v_options_2497_);
lean_inc(v_openDecls_2496_);
lean_inc(v_currNamespace_2495_);
lean_inc(v_imports_2494_);
lean_inc(v_sourceString_2493_);
lean_inc(v_index_2492_);
lean_dec(v_x2_2491_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2511_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v_toEnvExtension_2503_; lean_object* v_asyncMode_2504_; lean_object* v___x_2505_; lean_object* v___x_2507_; 
v___x_2502_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2503_ = lean_ctor_get(v___x_2502_, 0);
v_asyncMode_2504_ = lean_ctor_get(v_toEnvExtension_2503_, 2);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_declName_2489_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2505_);
v___x_2507_ = v___x_2500_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_index_2492_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_sourceString_2493_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v_imports_2494_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_currNamespace_2495_);
lean_ctor_set(v_reuseFailAlloc_2510_, 5, v_openDecls_2496_);
lean_ctor_set(v_reuseFailAlloc_2510_, 6, v_options_2497_);
lean_ctor_set(v_reuseFailAlloc_2510_, 7, v_check_2498_);
v___x_2507_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_box(0);
v___x_2509_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2502_, v_x1_2490_, v___x_2507_, v_asyncMode_2504_, v___x_2508_);
return v___x_2509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2532_, lean_object* v_docs_2533_, lean_object* v_deferred_2534_, lean_object* v___f_2535_, lean_object* v_env_2536_){
_start:
{
lean_object* v___x_2537_; lean_object* v_env_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2537_ = l_Lean_versoDocStringExt;
v_env_2538_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2537_, v_env_2536_, v_declName_2532_, v_docs_2533_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = lean_array_get_size(v_deferred_2534_);
v___x_2541_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2542_ = lean_nat_dec_lt(v___x_2539_, v___x_2540_);
if (v___x_2542_ == 0)
{
lean_dec_ref(v___f_2535_);
lean_dec_ref(v_deferred_2534_);
return v_env_2538_;
}
else
{
uint8_t v___x_2543_; 
v___x_2543_ = lean_nat_dec_le(v___x_2540_, v___x_2540_);
if (v___x_2543_ == 0)
{
if (v___x_2542_ == 0)
{
lean_dec_ref(v___f_2535_);
lean_dec_ref(v_deferred_2534_);
return v_env_2538_;
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2540_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2541_, v___f_2535_, v_deferred_2534_, v___x_2544_, v___x_2545_, v_env_2538_);
return v___x_2546_;
}
}
else
{
size_t v___x_2547_; size_t v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = lean_usize_of_nat(v___x_2540_);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2541_, v___f_2535_, v_deferred_2534_, v___x_2547_, v___x_2548_, v_env_2538_);
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2550_, lean_object* v___f_2551_, lean_object* v_____r_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_apply_1(v_modifyEnv_2550_, v___f_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2556_, lean_object* v_modifyEnv_2557_, lean_object* v___f_2558_, uint8_t v___x_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_toBind_2562_, lean_object* v___f_2563_, lean_object* v_____do__lift_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2564_, v_declName_2556_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; 
lean_dec(v___f_2563_);
lean_dec(v_toBind_2562_);
lean_dec_ref(v_inst_2561_);
lean_dec_ref(v_inst_2560_);
lean_dec(v_declName_2556_);
v___x_2566_ = lean_apply_1(v_modifyEnv_2557_, v___f_2558_);
return v___x_2566_;
}
else
{
lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2583_; 
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; 
v_unused_2584_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2584_);
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2583_;
goto v_resetjp_2567_;
}
else
{
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2583_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
if (v___x_2559_ == 0)
{
lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
lean_dec_ref(v___f_2558_);
lean_dec(v_modifyEnv_2557_);
v___x_2570_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2571_ = 1;
v___x_2572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2556_, v___x_2571_);
v___x_2573_ = lean_string_append(v___x_2570_, v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
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
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
v___x_2579_ = l_Lean_throwError___redArg(v_inst_2560_, v_inst_2561_, v___x_2578_);
v___x_2580_ = lean_apply_4(v_toBind_2562_, lean_box(0), lean_box(0), v___x_2579_, v___f_2563_);
return v___x_2580_;
}
}
else
{
lean_object* v___x_2582_; 
lean_del_object(v___x_2568_);
lean_dec(v___f_2563_);
lean_dec(v_toBind_2562_);
lean_dec_ref(v_inst_2561_);
lean_dec_ref(v_inst_2560_);
lean_dec(v_declName_2556_);
v___x_2582_ = lean_apply_1(v_modifyEnv_2557_, v___f_2558_);
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2585_, lean_object* v_modifyEnv_2586_, lean_object* v___f_2587_, lean_object* v___x_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_toBind_2591_, lean_object* v___f_2592_, lean_object* v_____do__lift_2593_){
_start:
{
uint8_t v___x_371__boxed_2594_; lean_object* v_res_2595_; 
v___x_371__boxed_2594_ = lean_unbox(v___x_2588_);
v_res_2595_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2585_, v_modifyEnv_2586_, v___f_2587_, v___x_371__boxed_2594_, v_inst_2589_, v_inst_2590_, v_toBind_2591_, v___f_2592_, v_____do__lift_2593_);
lean_dec_ref(v_____do__lift_2593_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_inst_2598_, lean_object* v_declName_2599_, lean_object* v_docs_2600_, lean_object* v_deferred_2601_){
_start:
{
lean_object* v_toApplicative_2602_; lean_object* v_toBind_2603_; lean_object* v_toPure_2604_; uint8_t v___x_2605_; 
v_toApplicative_2602_ = lean_ctor_get(v_inst_2596_, 0);
v_toBind_2603_ = lean_ctor_get(v_inst_2596_, 1);
lean_inc(v_toBind_2603_);
v_toPure_2604_ = lean_ctor_get(v_toApplicative_2602_, 1);
v___x_2605_ = l_Lean_Name_isAnonymous(v_declName_2599_);
if (v___x_2605_ == 0)
{
lean_object* v_getEnv_2606_; lean_object* v_modifyEnv_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; 
v_getEnv_2606_ = lean_ctor_get(v_inst_2597_, 0);
lean_inc(v_getEnv_2606_);
v_modifyEnv_2607_ = lean_ctor_get(v_inst_2597_, 1);
lean_inc_n(v_modifyEnv_2607_, 2);
lean_dec_ref(v_inst_2597_);
lean_inc_n(v_declName_2599_, 2);
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2608_, 0, v_declName_2599_);
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2609_, 0, v_declName_2599_);
lean_closure_set(v___f_2609_, 1, v_docs_2600_);
lean_closure_set(v___f_2609_, 2, v_deferred_2601_);
lean_closure_set(v___f_2609_, 3, v___f_2608_);
lean_inc_ref(v___f_2609_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2610_, 0, v_modifyEnv_2607_);
lean_closure_set(v___f_2610_, 1, v___f_2609_);
v___x_2611_ = lean_box(v___x_2605_);
lean_inc(v_toBind_2603_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2612_, 0, v_declName_2599_);
lean_closure_set(v___f_2612_, 1, v_modifyEnv_2607_);
lean_closure_set(v___f_2612_, 2, v___f_2609_);
lean_closure_set(v___f_2612_, 3, v___x_2611_);
lean_closure_set(v___f_2612_, 4, v_inst_2596_);
lean_closure_set(v___f_2612_, 5, v_inst_2598_);
lean_closure_set(v___f_2612_, 6, v_toBind_2603_);
lean_closure_set(v___f_2612_, 7, v___f_2610_);
v___x_2613_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v_getEnv_2606_, v___f_2612_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_inc(v_toPure_2604_);
lean_dec(v_toBind_2603_);
lean_dec_ref(v_deferred_2601_);
lean_dec_ref(v_docs_2600_);
lean_dec(v_declName_2599_);
lean_dec_ref(v_inst_2598_);
lean_dec_ref(v_inst_2597_);
lean_dec_ref(v_inst_2596_);
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_apply_2(v_toPure_2604_, lean_box(0), v___x_2614_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2616_, lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_declName_2621_, lean_object* v_docs_2622_, lean_object* v_deferred_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2617_, v_inst_2618_, v_inst_2620_, v_declName_2621_, v_docs_2622_, v_deferred_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_declName_2630_, lean_object* v_docs_2631_, lean_object* v_deferred_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_addVersoDocStringCore(v_m_2625_, v_inst_2626_, v_inst_2627_, v_inst_2628_, v_inst_2629_, v_declName_2630_, v_docs_2631_, v_deferred_2632_);
lean_dec(v_inst_2628_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2634_, lean_object* v_x1_2635_, lean_object* v_x2_2636_){
_start:
{
lean_object* v_index_2637_; lean_object* v_sourceString_2638_; lean_object* v_imports_2639_; lean_object* v_currNamespace_2640_; lean_object* v_openDecls_2641_; lean_object* v_options_2642_; lean_object* v_check_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2656_; 
v_index_2637_ = lean_ctor_get(v_x2_2636_, 1);
v_sourceString_2638_ = lean_ctor_get(v_x2_2636_, 2);
v_imports_2639_ = lean_ctor_get(v_x2_2636_, 3);
v_currNamespace_2640_ = lean_ctor_get(v_x2_2636_, 4);
v_openDecls_2641_ = lean_ctor_get(v_x2_2636_, 5);
v_options_2642_ = lean_ctor_get(v_x2_2636_, 6);
v_check_2643_ = lean_ctor_get(v_x2_2636_, 7);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_x2_2636_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v_x2_2636_, 0);
lean_dec(v_unused_2657_);
v___x_2645_ = v_x2_2636_;
v_isShared_2646_ = v_isSharedCheck_2656_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_check_2643_);
lean_inc(v_options_2642_);
lean_inc(v_openDecls_2641_);
lean_inc(v_currNamespace_2640_);
lean_inc(v_imports_2639_);
lean_inc(v_sourceString_2638_);
lean_inc(v_index_2637_);
lean_dec(v_x2_2636_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2656_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v_toEnvExtension_2648_; lean_object* v_asyncMode_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v___x_2647_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2648_ = lean_ctor_get(v___x_2647_, 0);
v_asyncMode_2649_ = lean_ctor_get(v_toEnvExtension_2648_, 2);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_size_2634_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v___x_2650_);
v___x_2652_ = v___x_2645_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2650_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_index_2637_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_sourceString_2638_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_imports_2639_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_currNamespace_2640_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v_openDecls_2641_);
lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_options_2642_);
lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_check_2643_);
v___x_2652_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2647_, v_x1_2635_, v___x_2652_, v_asyncMode_2649_, v___x_2653_);
return v___x_2654_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2660_ = l_Lean_stringToMessageData(v___x_2659_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_deferred_2664_, lean_object* v_inst_2665_, lean_object* v___f_2666_, lean_object* v_____do__lift_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2667_, v_docs_2661_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec_ref(v___f_2666_);
lean_dec_ref(v_inst_2665_);
lean_dec_ref(v_deferred_2664_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2671_ = l_Lean_stringToMessageData(v_a_2669_);
v___x_2672_ = l_Lean_indentD(v___x_2671_);
v___x_2673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2670_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_throwError___redArg(v_inst_2662_, v_inst_2663_, v___x_2673_);
return v___x_2674_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
lean_dec_ref(v_inst_2663_);
lean_dec_ref(v_inst_2662_);
v_a_2675_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = lean_array_get_size(v_deferred_2664_);
v___x_2678_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2679_ = lean_nat_dec_lt(v___x_2676_, v___x_2677_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
lean_dec_ref(v___f_2666_);
lean_dec_ref(v_deferred_2664_);
v___x_2680_ = l_Lean_setEnv___redArg(v_inst_2665_, v_a_2675_);
return v___x_2680_;
}
else
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_nat_dec_le(v___x_2677_, v___x_2677_);
if (v___x_2681_ == 0)
{
if (v___x_2679_ == 0)
{
lean_object* v___x_2682_; 
lean_dec_ref(v___f_2666_);
lean_dec_ref(v_deferred_2664_);
v___x_2682_ = l_Lean_setEnv___redArg(v_inst_2665_, v_a_2675_);
return v___x_2682_;
}
else
{
size_t v___x_2683_; size_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = lean_usize_of_nat(v___x_2677_);
v___x_2685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2678_, v___f_2666_, v_deferred_2664_, v___x_2683_, v___x_2684_, v_a_2675_);
v___x_2686_ = l_Lean_setEnv___redArg(v_inst_2665_, v___x_2685_);
return v___x_2686_;
}
}
else
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2687_ = ((size_t)0ULL);
v___x_2688_ = lean_usize_of_nat(v___x_2677_);
v___x_2689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2678_, v___f_2666_, v_deferred_2664_, v___x_2687_, v___x_2688_, v_a_2675_);
v___x_2690_ = l_Lean_setEnv___redArg(v_inst_2665_, v___x_2689_);
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_deferred_2694_, lean_object* v_inst_2695_, lean_object* v_toBind_2696_, lean_object* v_getEnv_2697_, lean_object* v_____do__lift_2698_){
_start:
{
lean_object* v___x_2699_; lean_object* v_size_2700_; lean_object* v___f_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; 
v___x_2699_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2698_);
v_size_2700_ = lean_ctor_get(v___x_2699_, 2);
lean_inc(v_size_2700_);
lean_dec_ref(v___x_2699_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2701_, 0, v_size_2700_);
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2702_, 0, v_docs_2691_);
lean_closure_set(v___f_2702_, 1, v_inst_2692_);
lean_closure_set(v___f_2702_, 2, v_inst_2693_);
lean_closure_set(v___f_2702_, 3, v_deferred_2694_);
lean_closure_set(v___f_2702_, 4, v_inst_2695_);
lean_closure_set(v___f_2702_, 5, v___f_2701_);
v___x_2703_ = lean_apply_4(v_toBind_2696_, lean_box(0), lean_box(0), v_getEnv_2697_, v___f_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2706_ = l_Lean_stringToMessageData(v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_toBind_2709_, lean_object* v_getEnv_2710_, lean_object* v___f_2711_, lean_object* v_____do__lift_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = l_Lean_getMainModuleDoc(v_____do__lift_2712_);
v___x_2714_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2713_);
lean_dec_ref(v___x_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v___f_2711_);
lean_dec(v_getEnv_2710_);
lean_dec(v_toBind_2709_);
v___x_2715_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2716_ = l_Lean_throwError___redArg(v_inst_2707_, v_inst_2708_, v___x_2715_);
return v___x_2716_;
}
else
{
lean_object* v___x_2717_; 
lean_dec_ref(v_inst_2708_);
lean_dec_ref(v_inst_2707_);
v___x_2717_ = lean_apply_4(v_toBind_2709_, lean_box(0), lean_box(0), v_getEnv_2710_, v___f_2711_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_docs_2721_, lean_object* v_deferred_2722_){
_start:
{
lean_object* v_toBind_2723_; lean_object* v_getEnv_2724_; lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; 
v_toBind_2723_ = lean_ctor_get(v_inst_2718_, 1);
lean_inc_n(v_toBind_2723_, 3);
v_getEnv_2724_ = lean_ctor_get(v_inst_2719_, 0);
lean_inc_n(v_getEnv_2724_, 3);
lean_inc_ref(v_inst_2720_);
lean_inc_ref(v_inst_2718_);
v___f_2725_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2725_, 0, v_docs_2721_);
lean_closure_set(v___f_2725_, 1, v_inst_2718_);
lean_closure_set(v___f_2725_, 2, v_inst_2720_);
lean_closure_set(v___f_2725_, 3, v_deferred_2722_);
lean_closure_set(v___f_2725_, 4, v_inst_2719_);
lean_closure_set(v___f_2725_, 5, v_toBind_2723_);
lean_closure_set(v___f_2725_, 6, v_getEnv_2724_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2726_, 0, v_inst_2718_);
lean_closure_set(v___f_2726_, 1, v_inst_2720_);
lean_closure_set(v___f_2726_, 2, v_toBind_2723_);
lean_closure_set(v___f_2726_, 3, v_getEnv_2724_);
lean_closure_set(v___f_2726_, 4, v___f_2725_);
v___x_2727_ = lean_apply_4(v_toBind_2723_, lean_box(0), lean_box(0), v_getEnv_2724_, v___f_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_docs_2733_, lean_object* v_deferred_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2729_, v_inst_2730_, v_inst_2732_, v_docs_2733_, v_deferred_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_docs_2741_, lean_object* v_deferred_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_addVersoModDocStringCore(v_m_2736_, v_inst_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_docs_2741_, v_deferred_2742_);
lean_dec(v_inst_2739_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2744_, lean_object* v_as_2745_, size_t v_i_2746_, size_t v_stop_2747_, lean_object* v_b_2748_){
_start:
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2746_, v_stop_2747_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_index_2751_; lean_object* v_sourceString_2752_; lean_object* v_imports_2753_; lean_object* v_currNamespace_2754_; lean_object* v_openDecls_2755_; lean_object* v_options_2756_; lean_object* v_check_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2773_; 
v___x_2750_ = lean_array_uget(v_as_2745_, v_i_2746_);
v_index_2751_ = lean_ctor_get(v___x_2750_, 1);
v_sourceString_2752_ = lean_ctor_get(v___x_2750_, 2);
v_imports_2753_ = lean_ctor_get(v___x_2750_, 3);
v_currNamespace_2754_ = lean_ctor_get(v___x_2750_, 4);
v_openDecls_2755_ = lean_ctor_get(v___x_2750_, 5);
v_options_2756_ = lean_ctor_get(v___x_2750_, 6);
v_check_2757_ = lean_ctor_get(v___x_2750_, 7);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; 
v_unused_2774_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2774_);
v___x_2759_ = v___x_2750_;
v_isShared_2760_ = v_isSharedCheck_2773_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_check_2757_);
lean_inc(v_options_2756_);
lean_inc(v_openDecls_2755_);
lean_inc(v_currNamespace_2754_);
lean_inc(v_imports_2753_);
lean_inc(v_sourceString_2752_);
lean_inc(v_index_2751_);
lean_dec(v___x_2750_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2773_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v_toEnvExtension_2762_; lean_object* v_asyncMode_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2761_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2762_ = lean_ctor_get(v___x_2761_, 0);
v_asyncMode_2763_ = lean_ctor_get(v_toEnvExtension_2762_, 2);
lean_inc(v_declName_2744_);
v___x_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2764_, 0, v_declName_2744_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2764_);
v___x_2766_ = v___x_2759_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_index_2751_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_sourceString_2752_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_imports_2753_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_currNamespace_2754_);
lean_ctor_set(v_reuseFailAlloc_2772_, 5, v_openDecls_2755_);
lean_ctor_set(v_reuseFailAlloc_2772_, 6, v_options_2756_);
lean_ctor_set(v_reuseFailAlloc_2772_, 7, v_check_2757_);
v___x_2766_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2761_, v_b_2748_, v___x_2766_, v_asyncMode_2763_, v___x_2767_);
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2746_, v___x_2769_);
v_i_2746_ = v___x_2770_;
v_b_2748_ = v___x_2768_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2744_);
return v_b_2748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2775_, lean_object* v_as_2776_, lean_object* v_i_2777_, lean_object* v_stop_2778_, lean_object* v_b_2779_){
_start:
{
size_t v_i_boxed_2780_; size_t v_stop_boxed_2781_; lean_object* v_res_2782_; 
v_i_boxed_2780_ = lean_unbox_usize(v_i_2777_);
lean_dec(v_i_2777_);
v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2778_);
lean_dec(v_stop_2778_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2775_, v_as_2776_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2779_);
lean_dec_ref(v_as_2776_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2789_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
lean_ctor_set(v___x_2789_, 2, v___x_2788_);
lean_ctor_set(v___x_2789_, 3, v___x_2788_);
lean_ctor_set(v___x_2789_, 4, v___x_2788_);
lean_ctor_set(v___x_2789_, 5, v___x_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2790_, lean_object* v_docs_2791_, lean_object* v_deferred_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2832_; lean_object* v___y_2833_; uint8_t v___x_2851_; 
v___x_2851_ = l_Lean_Name_isAnonymous(v_declName_2790_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v_env_2853_; lean_object* v___x_2854_; 
v___x_2852_ = lean_st_ref_get(v___y_2798_);
v_env_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_ref(v_env_2853_);
lean_dec(v___x_2852_);
v___x_2854_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2853_, v_declName_2790_);
lean_dec_ref(v_env_2853_);
if (lean_obj_tag(v___x_2854_) == 0)
{
v___y_2832_ = v___y_2796_;
v___y_2833_ = v___y_2798_;
goto v___jp_2831_;
}
else
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2869_; 
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v___x_2854_, 0);
lean_dec(v_unused_2870_);
v___x_2856_ = v___x_2854_;
v_isShared_2857_ = v_isSharedCheck_2869_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v___x_2854_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2869_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
if (v___x_2851_ == 0)
{
lean_object* v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
lean_dec_ref(v_docs_2791_);
v___x_2858_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2859_ = 1;
v___x_2860_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2790_, v___x_2859_);
v___x_2861_ = lean_string_append(v___x_2858_, v___x_2860_);
lean_dec_ref(v___x_2860_);
v___x_2862_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2863_ = lean_string_append(v___x_2861_, v___x_2862_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set_tag(v___x_2856_, 3);
lean_ctor_set(v___x_2856_, 0, v___x_2863_);
v___x_2865_ = v___x_2856_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = l_Lean_MessageData_ofFormat(v___x_2865_);
v___x_2867_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2866_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
return v___x_2867_;
}
}
else
{
lean_del_object(v___x_2856_);
v___y_2832_ = v___y_2796_;
v___y_2833_ = v___y_2798_;
goto v___jp_2831_;
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec_ref(v_docs_2791_);
lean_dec(v_declName_2790_);
v___x_2871_ = lean_box(0);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
v___jp_2800_:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v_mctx_2815_; lean_object* v_zetaDeltaFVarIds_2816_; lean_object* v_postponed_2817_; lean_object* v_diag_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2829_; 
v___x_2811_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2812_, 0, v___y_2810_);
lean_ctor_set(v___x_2812_, 1, v___y_2803_);
lean_ctor_set(v___x_2812_, 2, v___y_2807_);
lean_ctor_set(v___x_2812_, 3, v___y_2805_);
lean_ctor_set(v___x_2812_, 4, v___y_2809_);
lean_ctor_set(v___x_2812_, 5, v___x_2811_);
lean_ctor_set(v___x_2812_, 6, v___y_2808_);
lean_ctor_set(v___x_2812_, 7, v___y_2802_);
lean_ctor_set(v___x_2812_, 8, v___y_2806_);
v___x_2813_ = lean_st_ref_put(v___y_2801_, v___x_2812_);
v___x_2814_ = lean_st_ref_take(v___y_2804_);
v_mctx_2815_ = lean_ctor_get(v___x_2814_, 0);
v_zetaDeltaFVarIds_2816_ = lean_ctor_get(v___x_2814_, 2);
v_postponed_2817_ = lean_ctor_get(v___x_2814_, 3);
v_diag_2818_ = lean_ctor_get(v___x_2814_, 4);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v___x_2814_, 1);
lean_dec(v_unused_2830_);
v___x_2820_ = v___x_2814_;
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_diag_2818_);
lean_inc(v_postponed_2817_);
lean_inc(v_zetaDeltaFVarIds_2816_);
lean_inc(v_mctx_2815_);
lean_dec(v___x_2814_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 1, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_mctx_2815_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v___x_2822_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_zetaDeltaFVarIds_2816_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_postponed_2817_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_diag_2818_);
v___x_2824_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2825_ = lean_st_ref_put(v___y_2804_, v___x_2824_);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2834_; lean_object* v_env_2835_; lean_object* v_nextMacroScope_2836_; lean_object* v_ngen_2837_; lean_object* v_auxDeclNGen_2838_; lean_object* v_traceState_2839_; lean_object* v_messages_2840_; lean_object* v_infoState_2841_; lean_object* v_snapshotTasks_2842_; lean_object* v___x_2843_; lean_object* v_env_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; uint8_t v___x_2847_; 
v___x_2834_ = lean_st_ref_take(v___y_2833_);
v_env_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_env_2835_);
v_nextMacroScope_2836_ = lean_ctor_get(v___x_2834_, 1);
lean_inc(v_nextMacroScope_2836_);
v_ngen_2837_ = lean_ctor_get(v___x_2834_, 2);
lean_inc_ref(v_ngen_2837_);
v_auxDeclNGen_2838_ = lean_ctor_get(v___x_2834_, 3);
lean_inc_ref(v_auxDeclNGen_2838_);
v_traceState_2839_ = lean_ctor_get(v___x_2834_, 4);
lean_inc_ref(v_traceState_2839_);
v_messages_2840_ = lean_ctor_get(v___x_2834_, 6);
lean_inc_ref(v_messages_2840_);
v_infoState_2841_ = lean_ctor_get(v___x_2834_, 7);
lean_inc_ref(v_infoState_2841_);
v_snapshotTasks_2842_ = lean_ctor_get(v___x_2834_, 8);
lean_inc_ref(v_snapshotTasks_2842_);
lean_dec(v___x_2834_);
v___x_2843_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2790_);
v_env_2844_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2843_, v_env_2835_, v_declName_2790_, v_docs_2791_);
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = lean_array_get_size(v_deferred_2792_);
v___x_2847_ = lean_nat_dec_lt(v___x_2845_, v___x_2846_);
if (v___x_2847_ == 0)
{
lean_dec(v_declName_2790_);
v___y_2801_ = v___y_2833_;
v___y_2802_ = v_infoState_2841_;
v___y_2803_ = v_nextMacroScope_2836_;
v___y_2804_ = v___y_2832_;
v___y_2805_ = v_auxDeclNGen_2838_;
v___y_2806_ = v_snapshotTasks_2842_;
v___y_2807_ = v_ngen_2837_;
v___y_2808_ = v_messages_2840_;
v___y_2809_ = v_traceState_2839_;
v___y_2810_ = v_env_2844_;
goto v___jp_2800_;
}
else
{
size_t v___x_2848_; size_t v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = ((size_t)0ULL);
v___x_2849_ = lean_usize_of_nat(v___x_2846_);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2790_, v_deferred_2792_, v___x_2848_, v___x_2849_, v_env_2844_);
v___y_2801_ = v___y_2833_;
v___y_2802_ = v_infoState_2841_;
v___y_2803_ = v_nextMacroScope_2836_;
v___y_2804_ = v___y_2832_;
v___y_2805_ = v_auxDeclNGen_2838_;
v___y_2806_ = v_snapshotTasks_2842_;
v___y_2807_ = v_ngen_2837_;
v___y_2808_ = v_messages_2840_;
v___y_2809_ = v_traceState_2839_;
v___y_2810_ = v___x_2850_;
goto v___jp_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2873_, lean_object* v_docs_2874_, lean_object* v_deferred_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2873_, v_docs_2874_, v_deferred_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_deferred_2875_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2884_, lean_object* v_binders_2885_, lean_object* v_docComment_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___x_2914_; lean_object* v_env_2915_; lean_object* v___x_2916_; 
v___x_2914_ = lean_st_ref_get(v_a_2892_);
v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc_ref(v_env_2915_);
lean_dec(v___x_2914_);
v___x_2916_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2915_, v_declName_2884_);
lean_dec_ref(v_env_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
v___y_2895_ = v_a_2887_;
v___y_2896_ = v_a_2888_;
v___y_2897_ = v_a_2889_;
v___y_2898_ = v_a_2890_;
v___y_2899_ = v_a_2891_;
v___y_2900_ = v_a_2892_;
goto v___jp_2894_;
}
else
{
lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2931_; 
lean_dec(v_docComment_2886_);
lean_dec(v_binders_2885_);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v___x_2916_, 0);
lean_dec(v_unused_2932_);
v___x_2918_ = v___x_2916_;
v_isShared_2919_ = v_isSharedCheck_2931_;
goto v_resetjp_2917_;
}
else
{
lean_dec(v___x_2916_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2931_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2920_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2921_ = 1;
v___x_2922_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2884_, v___x_2921_);
v___x_2923_ = lean_string_append(v___x_2920_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___x_2924_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2925_ = lean_string_append(v___x_2923_, v___x_2924_);
if (v_isShared_2919_ == 0)
{
lean_ctor_set_tag(v___x_2918_, 3);
lean_ctor_set(v___x_2918_, 0, v___x_2925_);
v___x_2927_ = v___x_2918_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = l_Lean_MessageData_ofFormat(v___x_2927_);
v___x_2929_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2928_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
return v___x_2929_;
}
}
}
v___jp_2894_:
{
lean_object* v___x_2901_; 
lean_inc(v_declName_2884_);
v___x_2901_ = l_Lean_versoDocString(v_declName_2884_, v_binders_2885_, v_docComment_2886_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_toVersoDocString_2903_; lean_object* v_deferredChecks_2904_; lean_object* v___x_2905_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v_toVersoDocString_2903_ = lean_ctor_get(v_a_2902_, 0);
lean_inc_ref(v_toVersoDocString_2903_);
v_deferredChecks_2904_ = lean_ctor_get(v_a_2902_, 1);
lean_inc_ref(v_deferredChecks_2904_);
lean_dec(v_a_2902_);
v___x_2905_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2884_, v_toVersoDocString_2903_, v_deferredChecks_2904_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec_ref(v_deferredChecks_2904_);
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_declName_2884_);
v_a_2906_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2901_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2901_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2933_, lean_object* v_binders_2934_, lean_object* v_docComment_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_addVersoDocString(v_declName_2933_, v_binders_2934_, v_docComment_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2944_, lean_object* v_docComment_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___x_2973_; lean_object* v_env_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_st_ref_get(v_a_2951_);
v_env_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_ref(v_env_2974_);
lean_dec(v___x_2973_);
v___x_2975_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2974_, v_declName_2944_);
lean_dec_ref(v_env_2974_);
if (lean_obj_tag(v___x_2975_) == 0)
{
v___y_2954_ = v_a_2946_;
v___y_2955_ = v_a_2947_;
v___y_2956_ = v_a_2948_;
v___y_2957_ = v_a_2949_;
v___y_2958_ = v_a_2950_;
v___y_2959_ = v_a_2951_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_docComment_2945_);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2991_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2990_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2990_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2979_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2980_ = 1;
v___x_2981_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2944_, v___x_2980_);
v___x_2982_ = lean_string_append(v___x_2979_, v___x_2981_);
lean_dec_ref(v___x_2981_);
v___x_2983_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2984_ = lean_string_append(v___x_2982_, v___x_2983_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 3);
lean_ctor_set(v___x_2977_, 0, v___x_2984_);
v___x_2986_ = v___x_2977_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_MessageData_ofFormat(v___x_2986_);
v___x_2988_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2987_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v___x_2988_;
}
}
}
v___jp_2953_:
{
lean_object* v___x_2960_; 
lean_inc(v_declName_2944_);
v___x_2960_ = l_Lean_versoDocStringFromString(v_declName_2944_, v_docComment_2945_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v_toVersoDocString_2962_; lean_object* v_deferredChecks_2963_; lean_object* v___x_2964_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v_toVersoDocString_2962_ = lean_ctor_get(v_a_2961_, 0);
lean_inc_ref(v_toVersoDocString_2962_);
v_deferredChecks_2963_ = lean_ctor_get(v_a_2961_, 1);
lean_inc_ref(v_deferredChecks_2963_);
lean_dec(v_a_2961_);
v___x_2964_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2944_, v_toVersoDocString_2962_, v_deferredChecks_2963_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
lean_dec_ref(v_deferredChecks_2963_);
return v___x_2964_;
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_declName_2944_);
v_a_2965_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2960_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2960_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
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
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2992_, lean_object* v_docComment_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lean_addVersoDocStringFromString(v_declName_2992_, v_docComment_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
lean_dec(v_a_2999_);
lean_dec_ref(v_a_2998_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3002_, lean_object* v_msgData_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = 2;
v___x_3010_ = 0;
v___x_3011_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_3002_, v_msgData_3003_, v___x_3009_, v___x_3010_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3012_, lean_object* v_msgData_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3012_, v_msgData_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v_ref_3012_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3020_, lean_object* v_str_3021_, lean_object* v_as_3022_, size_t v_sz_3023_, size_t v_i_3024_, lean_object* v_b_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_a_3034_; uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_lt(v_i_3024_, v_sz_3023_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_b_3025_);
return v___x_3039_;
}
else
{
lean_object* v_a_3040_; lean_object* v_fst_3041_; lean_object* v_snd_3042_; lean_object* v_start_3043_; lean_object* v_stop_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3064_; 
v_a_3040_ = lean_array_uget_borrowed(v_as_3022_, v_i_3024_);
v_fst_3041_ = lean_ctor_get(v_a_3040_, 0);
lean_inc(v_fst_3041_);
v_snd_3042_ = lean_ctor_get(v_a_3040_, 1);
v_start_3043_ = lean_ctor_get(v_fst_3041_, 0);
v_stop_3044_ = lean_ctor_get(v_fst_3041_, 1);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_fst_3041_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3046_ = v_fst_3041_;
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_stop_3044_);
lean_inc(v_start_3043_);
lean_dec(v_fst_3041_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3064_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_box(0);
if (lean_obj_tag(v___y_3020_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v_val_3049_ = lean_ctor_get(v___y_3020_, 0);
v___x_3050_ = lean_nat_add(v_val_3049_, v_start_3043_);
v___x_3051_ = lean_nat_add(v_val_3049_, v_stop_3044_);
v___x_3052_ = 0;
v___x_3053_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3053_, 0, v___x_3050_);
lean_ctor_set(v___x_3053_, 1, v___x_3051_);
lean_ctor_set_uint8(v___x_3053_, sizeof(void*)*2, v___x_3052_);
v___x_3054_ = lean_string_utf8_extract(v_str_3021_, v_start_3043_, v_stop_3044_);
lean_dec(v_stop_3044_);
lean_dec(v_start_3043_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 2);
lean_ctor_set(v___x_3046_, 1, v___x_3054_);
lean_ctor_set(v___x_3046_, 0, v___x_3053_);
v___x_3056_ = v___x_3046_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_inc(v_snd_3042_);
v___x_3057_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_snd_3042_);
v___x_3058_ = l_Lean_MessageData_ofFormat(v___x_3057_);
v___x_3059_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3056_, v___x_3058_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec_ref(v___x_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref_known(v___x_3059_, 1);
v_a_3034_ = v___x_3048_;
goto v___jp_3033_;
}
else
{
return v___x_3059_;
}
}
}
else
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_del_object(v___x_3046_);
lean_dec(v_stop_3044_);
lean_dec(v_start_3043_);
lean_inc(v_snd_3042_);
v___x_3061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_snd_3042_);
v___x_3062_ = l_Lean_MessageData_ofFormat(v___x_3061_);
v___x_3063_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3062_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_dec_ref_known(v___x_3063_, 1);
v_a_3034_ = v___x_3048_;
goto v___jp_3033_;
}
else
{
return v___x_3063_;
}
}
}
}
v___jp_3033_:
{
size_t v___x_3035_; size_t v___x_3036_; 
v___x_3035_ = ((size_t)1ULL);
v___x_3036_ = lean_usize_add(v_i_3024_, v___x_3035_);
v_i_3024_ = v___x_3036_;
v_b_3025_ = v_a_3034_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3065_, lean_object* v_str_3066_, lean_object* v_as_3067_, lean_object* v_sz_3068_, lean_object* v_i_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
size_t v_sz_boxed_3078_; size_t v_i_boxed_3079_; lean_object* v_res_3080_; 
v_sz_boxed_3078_ = lean_unbox_usize(v_sz_3068_);
lean_dec(v_sz_3068_);
v_i_boxed_3079_ = lean_unbox_usize(v_i_3069_);
lean_dec(v_i_3069_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3065_, v_str_3066_, v_as_3067_, v_sz_boxed_3078_, v_i_boxed_3079_, v_b_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_as_3067_);
lean_dec_ref(v_str_3066_);
lean_dec(v___y_3065_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_str_3089_; lean_object* v___y_3091_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_str_3089_ = l_Lean_TSyntax_getDocString(v_docstring_3081_);
v___x_3106_ = lean_unsigned_to_nat(1u);
v___x_3107_ = l_Lean_Syntax_getArg(v_docstring_3081_, v___x_3106_);
v___x_3108_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3107_);
lean_dec(v___x_3107_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_box(0);
v___y_3091_ = v___x_3109_;
goto v___jp_3090_;
}
else
{
lean_object* v_val_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; 
v_val_3110_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_val_3110_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3111_ = 0;
v___x_3112_ = l_Lean_SourceInfo_getPos_x3f(v_val_3110_, v___x_3111_);
lean_dec(v_val_3110_);
v___y_3091_ = v___x_3112_;
goto v___jp_3090_;
}
v___jp_3090_:
{
lean_object* v___x_3092_; lean_object* v_fst_3093_; lean_object* v___x_3094_; size_t v_sz_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
lean_inc_ref(v_str_3089_);
v___x_3092_ = l_Lean_rewriteManualLinksCore(v_str_3089_);
v_fst_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_fst_3093_);
lean_dec_ref(v___x_3092_);
v___x_3094_ = lean_box(0);
v_sz_3095_ = lean_array_size(v_fst_3093_);
v___x_3096_ = ((size_t)0ULL);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3091_, v_str_3089_, v_fst_3093_, v_sz_3095_, v___x_3096_, v___x_3094_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v_fst_3093_);
lean_dec_ref(v_str_3089_);
lean_dec(v___y_3091_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; 
v_unused_3105_ = lean_ctor_get(v___x_3097_, 0);
lean_dec(v_unused_3105_);
v___x_3099_ = v___x_3097_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v___x_3097_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3094_);
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3094_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
else
{
return v___x_3097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v_docstring_3113_);
return v_res_3121_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3124_ = l_Lean_stringToMessageData(v___x_3123_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_val_3140_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = l_Lean_Syntax_getArg(v_stx_3125_, v___x_3147_);
switch(lean_obj_tag(v___x_3148_))
{
case 2:
{
lean_object* v_val_3149_; 
lean_dec(v_stx_3125_);
v_val_3149_ = lean_ctor_get(v___x_3148_, 1);
lean_inc_ref(v_val_3149_);
lean_dec_ref_known(v___x_3148_, 2);
v_val_3140_ = v_val_3149_;
goto v___jp_3139_;
}
case 1:
{
lean_object* v_kind_3150_; 
v_kind_3150_ = lean_ctor_get(v___x_3148_, 1);
lean_inc(v_kind_3150_);
if (lean_obj_tag(v_kind_3150_) == 1)
{
lean_object* v_pre_3151_; 
v_pre_3151_ = lean_ctor_get(v_kind_3150_, 0);
lean_inc(v_pre_3151_);
if (lean_obj_tag(v_pre_3151_) == 1)
{
lean_object* v_pre_3152_; 
v_pre_3152_ = lean_ctor_get(v_pre_3151_, 0);
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
if (lean_obj_tag(v_pre_3154_) == 0)
{
lean_object* v_str_3155_; lean_object* v_str_3156_; lean_object* v_str_3157_; lean_object* v_str_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v_str_3155_ = lean_ctor_get(v_kind_3150_, 1);
lean_inc_ref(v_str_3155_);
lean_dec_ref_known(v_kind_3150_, 2);
v_str_3156_ = lean_ctor_get(v_pre_3151_, 1);
lean_inc_ref(v_str_3156_);
lean_dec_ref_known(v_pre_3151_, 2);
v_str_3157_ = lean_ctor_get(v_pre_3152_, 1);
lean_inc_ref(v_str_3157_);
lean_dec_ref_known(v_pre_3152_, 2);
v_str_3158_ = lean_ctor_get(v_pre_3153_, 1);
lean_inc_ref(v_str_3158_);
lean_dec_ref_known(v_pre_3153_, 2);
v___x_3159_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3160_ = lean_string_dec_eq(v_str_3158_, v___x_3159_);
lean_dec_ref(v_str_3158_);
if (v___x_3160_ == 0)
{
lean_dec_ref(v_str_3157_);
lean_dec_ref(v_str_3156_);
lean_dec_ref(v_str_3155_);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
else
{
lean_object* v___x_3161_; uint8_t v___x_3162_; 
v___x_3161_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3162_ = lean_string_dec_eq(v_str_3157_, v___x_3161_);
lean_dec_ref(v_str_3157_);
if (v___x_3162_ == 0)
{
lean_dec_ref(v_str_3156_);
lean_dec_ref(v_str_3155_);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
else
{
lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3163_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3164_ = lean_string_dec_eq(v_str_3156_, v___x_3163_);
lean_dec_ref(v_str_3156_);
if (v___x_3164_ == 0)
{
lean_dec_ref(v_str_3155_);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
else
{
lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3166_ = lean_string_dec_eq(v_str_3155_, v___x_3165_);
lean_dec_ref(v_str_3155_);
if (v___x_3166_ == 0)
{
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
else
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3168_ = l_Lean_Syntax_getArg(v___x_3148_, v___x_3167_);
lean_dec_ref_known(v___x_3148_, 3);
if (lean_obj_tag(v___x_3168_) == 2)
{
lean_object* v_val_3169_; 
lean_dec(v_stx_3125_);
v_val_3169_ = lean_ctor_get(v___x_3168_, 1);
lean_inc_ref(v_val_3169_);
lean_dec_ref_known(v___x_3168_, 2);
v_val_3140_ = v_val_3169_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v___x_3168_);
v___x_3170_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3125_);
v___x_3171_ = l_Lean_MessageData_ofSyntax(v_stx_3125_);
v___x_3172_ = l_Lean_indentD(v___x_3171_);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3170_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3125_, v___x_3173_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v_stx_3125_);
return v___x_3174_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3153_, 2);
lean_dec_ref_known(v_pre_3152_, 2);
lean_dec_ref_known(v_pre_3151_, 2);
lean_dec_ref_known(v_kind_3150_, 2);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
}
else
{
lean_dec(v_pre_3153_);
lean_dec_ref_known(v_pre_3152_, 2);
lean_dec_ref_known(v_pre_3151_, 2);
lean_dec_ref_known(v_kind_3150_, 2);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
}
else
{
lean_dec_ref_known(v_pre_3151_, 2);
lean_dec(v_pre_3152_);
lean_dec_ref_known(v_kind_3150_, 2);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
}
else
{
lean_dec_ref_known(v_kind_3150_, 2);
lean_dec(v_pre_3151_);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
}
else
{
lean_dec(v_kind_3150_);
lean_dec_ref_known(v___x_3148_, 3);
goto v___jp_3133_;
}
}
default: 
{
lean_dec(v___x_3148_);
goto v___jp_3133_;
}
}
v___jp_3133_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3134_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3125_);
v___x_3135_ = l_Lean_MessageData_ofSyntax(v_stx_3125_);
v___x_3136_ = l_Lean_indentD(v___x_3135_);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3134_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3125_, v___x_3137_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v_stx_3125_);
return v___x_3138_;
}
v___jp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = lean_string_utf8_byte_size(v_val_3140_);
v___x_3143_ = lean_unsigned_to_nat(2u);
v___x_3144_ = lean_nat_sub(v___x_3142_, v___x_3143_);
v___x_3145_ = lean_string_utf8_extract(v_val_3140_, v___x_3141_, v___x_3144_);
lean_dec(v___x_3144_);
lean_dec_ref(v_val_3140_);
v___x_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3184_, lean_object* v_docComment_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; uint8_t v___x_3256_; 
v___x_3256_ = l_Lean_Name_isAnonymous(v_declName_3184_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v___x_3259_; 
v___x_3257_ = lean_st_ref_get(v___y_3191_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3258_);
lean_dec(v___x_3257_);
v___x_3259_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3258_, v_declName_3184_);
lean_dec_ref(v_env_3258_);
if (lean_obj_tag(v___x_3259_) == 0)
{
v___y_3194_ = v___y_3186_;
v___y_3195_ = v___y_3187_;
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
goto v___jp_3193_;
}
else
{
lean_dec_ref_known(v___x_3259_, 1);
if (v___x_3256_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_docComment_3185_);
v___x_3260_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3261_ = l_Lean_MessageData_ofConstName(v_declName_3184_, v___x_3256_);
v___x_3262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3260_);
lean_ctor_set(v___x_3262_, 1, v___x_3261_);
v___x_3263_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3262_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3264_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
return v___x_3265_;
}
else
{
v___y_3194_ = v___y_3186_;
v___y_3195_ = v___y_3187_;
v___y_3196_ = v___y_3188_;
v___y_3197_ = v___y_3189_;
v___y_3198_ = v___y_3190_;
v___y_3199_ = v___y_3191_;
goto v___jp_3193_;
}
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec(v_docComment_3185_);
lean_dec(v_declName_3184_);
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
return v___x_3267_;
}
v___jp_3193_:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3185_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v___x_3201_; 
lean_dec_ref_known(v___x_3200_, 1);
v___x_3201_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3185_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3247_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3247_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3247_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v_env_3207_; lean_object* v_nextMacroScope_3208_; lean_object* v_ngen_3209_; lean_object* v_auxDeclNGen_3210_; lean_object* v_traceState_3211_; lean_object* v_messages_3212_; lean_object* v_infoState_3213_; lean_object* v_snapshotTasks_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3245_; 
v___x_3206_ = lean_st_ref_take(v___y_3199_);
v_env_3207_ = lean_ctor_get(v___x_3206_, 0);
v_nextMacroScope_3208_ = lean_ctor_get(v___x_3206_, 1);
v_ngen_3209_ = lean_ctor_get(v___x_3206_, 2);
v_auxDeclNGen_3210_ = lean_ctor_get(v___x_3206_, 3);
v_traceState_3211_ = lean_ctor_get(v___x_3206_, 4);
v_messages_3212_ = lean_ctor_get(v___x_3206_, 6);
v_infoState_3213_ = lean_ctor_get(v___x_3206_, 7);
v_snapshotTasks_3214_ = lean_ctor_get(v___x_3206_, 8);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v___x_3206_, 5);
lean_dec(v_unused_3246_);
v___x_3216_ = v___x_3206_;
v_isShared_3217_ = v_isSharedCheck_3245_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_snapshotTasks_3214_);
lean_inc(v_infoState_3213_);
lean_inc(v_messages_3212_);
lean_inc(v_traceState_3211_);
lean_inc(v_auxDeclNGen_3210_);
lean_inc(v_ngen_3209_);
lean_inc(v_nextMacroScope_3208_);
lean_inc(v_env_3207_);
lean_dec(v___x_3206_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3245_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3218_ = l_Lean_docStringExt;
v___x_3219_ = l_String_removeLeadingSpaces(v_a_3202_);
v___x_3220_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3218_, v_env_3207_, v_declName_3184_, v___x_3219_);
v___x_3221_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 5, v___x_3221_);
lean_ctor_set(v___x_3216_, 0, v___x_3220_);
v___x_3223_ = v___x_3216_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_nextMacroScope_3208_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_ngen_3209_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_auxDeclNGen_3210_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_traceState_3211_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_messages_3212_);
lean_ctor_set(v_reuseFailAlloc_3244_, 7, v_infoState_3213_);
lean_ctor_set(v_reuseFailAlloc_3244_, 8, v_snapshotTasks_3214_);
v___x_3223_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_mctx_3226_; lean_object* v_zetaDeltaFVarIds_3227_; lean_object* v_postponed_3228_; lean_object* v_diag_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3242_; 
v___x_3224_ = lean_st_ref_put(v___y_3199_, v___x_3223_);
v___x_3225_ = lean_st_ref_take(v___y_3197_);
v_mctx_3226_ = lean_ctor_get(v___x_3225_, 0);
v_zetaDeltaFVarIds_3227_ = lean_ctor_get(v___x_3225_, 2);
v_postponed_3228_ = lean_ctor_get(v___x_3225_, 3);
v_diag_3229_ = lean_ctor_get(v___x_3225_, 4);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3225_, 1);
lean_dec(v_unused_3243_);
v___x_3231_ = v___x_3225_;
v_isShared_3232_ = v_isSharedCheck_3242_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_diag_3229_);
lean_inc(v_postponed_3228_);
lean_inc(v_zetaDeltaFVarIds_3227_);
lean_inc(v_mctx_3226_);
lean_dec(v___x_3225_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3242_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 1, v___x_3233_);
v___x_3235_ = v___x_3231_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_mctx_3226_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_zetaDeltaFVarIds_3227_);
lean_ctor_set(v_reuseFailAlloc_3241_, 3, v_postponed_3228_);
lean_ctor_set(v_reuseFailAlloc_3241_, 4, v_diag_3229_);
v___x_3235_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3236_ = lean_st_ref_put(v___y_3197_, v___x_3235_);
v___x_3237_ = lean_box(0);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3237_);
v___x_3239_ = v___x_3204_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
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
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_declName_3184_);
v_a_3248_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3201_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3201_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_dec(v_docComment_3185_);
lean_dec(v_declName_3184_);
return v___x_3200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3268_, lean_object* v_docComment_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3268_, v_docComment_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3278_, lean_object* v_declName_3279_, lean_object* v_binders_3280_, lean_object* v_docComment_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
if (v_isVerso_3278_ == 0)
{
lean_object* v___x_3289_; 
lean_dec(v_binders_3280_);
v___x_3289_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3279_, v_docComment_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_addVersoDocString(v_declName_3279_, v_binders_3280_, v_docComment_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3291_, lean_object* v_declName_3292_, lean_object* v_binders_3293_, lean_object* v_docComment_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
uint8_t v_isVerso_boxed_3302_; lean_object* v_res_3303_; 
v_isVerso_boxed_3302_ = lean_unbox(v_isVerso_3291_);
v_res_3303_ = l_Lean_addDocStringOf(v_isVerso_boxed_3302_, v_declName_3292_, v_binders_3293_, v_docComment_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3304_, lean_object* v_msgData_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3304_, v_msgData_3305_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3314_, lean_object* v_msgData_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3314_, v_msgData_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v_ref_3314_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3324_, lean_object* v_t_3325_){
_start:
{
if (lean_obj_tag(v_t_3325_) == 0)
{
lean_object* v_k_3326_; lean_object* v_v_3327_; lean_object* v_l_3328_; lean_object* v_r_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3983_; 
v_k_3326_ = lean_ctor_get(v_t_3325_, 1);
v_v_3327_ = lean_ctor_get(v_t_3325_, 2);
v_l_3328_ = lean_ctor_get(v_t_3325_, 3);
v_r_3329_ = lean_ctor_get(v_t_3325_, 4);
v_isSharedCheck_3983_ = !lean_is_exclusive(v_t_3325_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v_t_3325_, 0);
lean_dec(v_unused_3984_);
v___x_3331_ = v_t_3325_;
v_isShared_3332_ = v_isSharedCheck_3983_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_r_3329_);
lean_inc(v_l_3328_);
lean_inc(v_v_3327_);
lean_inc(v_k_3326_);
lean_dec(v_t_3325_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3983_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
uint8_t v___x_3333_; 
v___x_3333_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3324_, v_k_3326_);
switch(v___x_3333_)
{
case 0:
{
lean_object* v_impl_3334_; lean_object* v___x_3335_; 
v_impl_3334_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3324_, v_l_3328_);
v___x_3335_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3334_) == 0)
{
if (lean_obj_tag(v_r_3329_) == 0)
{
lean_object* v_size_3336_; lean_object* v_size_3337_; lean_object* v_k_3338_; lean_object* v_v_3339_; lean_object* v_l_3340_; lean_object* v_r_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_size_3336_ = lean_ctor_get(v_impl_3334_, 0);
lean_inc(v_size_3336_);
v_size_3337_ = lean_ctor_get(v_r_3329_, 0);
v_k_3338_ = lean_ctor_get(v_r_3329_, 1);
v_v_3339_ = lean_ctor_get(v_r_3329_, 2);
v_l_3340_ = lean_ctor_get(v_r_3329_, 3);
lean_inc(v_l_3340_);
v_r_3341_ = lean_ctor_get(v_r_3329_, 4);
v___x_3342_ = lean_unsigned_to_nat(3u);
v___x_3343_ = lean_nat_mul(v___x_3342_, v_size_3336_);
v___x_3344_ = lean_nat_dec_lt(v___x_3343_, v_size_3337_);
lean_dec(v___x_3343_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_dec(v_l_3340_);
v___x_3345_ = lean_nat_add(v___x_3335_, v_size_3336_);
lean_dec(v_size_3336_);
v___x_3346_ = lean_nat_add(v___x_3345_, v_size_3337_);
lean_dec(v___x_3345_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 3, v_impl_3334_);
lean_ctor_set(v___x_3331_, 0, v___x_3346_);
v___x_3348_ = v___x_3331_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_impl_3334_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_r_3329_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
else
{
lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3413_; 
lean_inc(v_r_3341_);
lean_inc(v_v_3339_);
lean_inc(v_k_3338_);
lean_inc(v_size_3337_);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; lean_object* v_unused_3415_; lean_object* v_unused_3416_; lean_object* v_unused_3417_; lean_object* v_unused_3418_; 
v_unused_3414_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3414_);
v_unused_3415_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3415_);
v_unused_3416_ = lean_ctor_get(v_r_3329_, 2);
lean_dec(v_unused_3416_);
v_unused_3417_ = lean_ctor_get(v_r_3329_, 1);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3418_);
v___x_3351_ = v_r_3329_;
v_isShared_3352_ = v_isSharedCheck_3413_;
goto v_resetjp_3350_;
}
else
{
lean_dec(v_r_3329_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3413_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_size_3353_; lean_object* v_k_3354_; lean_object* v_v_3355_; lean_object* v_l_3356_; lean_object* v_r_3357_; lean_object* v_size_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v_size_3353_ = lean_ctor_get(v_l_3340_, 0);
v_k_3354_ = lean_ctor_get(v_l_3340_, 1);
v_v_3355_ = lean_ctor_get(v_l_3340_, 2);
v_l_3356_ = lean_ctor_get(v_l_3340_, 3);
v_r_3357_ = lean_ctor_get(v_l_3340_, 4);
v_size_3358_ = lean_ctor_get(v_r_3341_, 0);
v___x_3359_ = lean_unsigned_to_nat(2u);
v___x_3360_ = lean_nat_mul(v___x_3359_, v_size_3358_);
v___x_3361_ = lean_nat_dec_lt(v_size_3353_, v___x_3360_);
lean_dec(v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3389_; 
lean_inc(v_r_3357_);
lean_inc(v_l_3356_);
lean_inc(v_v_3355_);
lean_inc(v_k_3354_);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; lean_object* v_unused_3391_; lean_object* v_unused_3392_; lean_object* v_unused_3393_; lean_object* v_unused_3394_; 
v_unused_3390_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3390_);
v_unused_3391_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3391_);
v_unused_3392_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3392_);
v_unused_3393_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3393_);
v_unused_3394_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3394_);
v___x_3363_ = v_l_3340_;
v_isShared_3364_ = v_isSharedCheck_3389_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v_l_3340_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3389_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3379_; 
v___x_3365_ = lean_nat_add(v___x_3335_, v_size_3336_);
lean_dec(v_size_3336_);
v___x_3366_ = lean_nat_add(v___x_3365_, v_size_3337_);
lean_dec(v_size_3337_);
if (lean_obj_tag(v_l_3356_) == 0)
{
lean_object* v_size_3387_; 
v_size_3387_ = lean_ctor_get(v_l_3356_, 0);
lean_inc(v_size_3387_);
v___y_3379_ = v_size_3387_;
goto v___jp_3378_;
}
else
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_unsigned_to_nat(0u);
v___y_3379_ = v___x_3388_;
goto v___jp_3378_;
}
v___jp_3367_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_nat_add(v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 4, v_r_3341_);
lean_ctor_set(v___x_3363_, 3, v_r_3357_);
lean_ctor_set(v___x_3363_, 2, v_v_3339_);
lean_ctor_set(v___x_3363_, 1, v_k_3338_);
lean_ctor_set(v___x_3363_, 0, v___x_3371_);
v___x_3373_ = v___x_3363_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_r_3357_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v_r_3341_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 4, v___x_3373_);
lean_ctor_set(v___x_3351_, 3, v___y_3368_);
lean_ctor_set(v___x_3351_, 2, v_v_3355_);
lean_ctor_set(v___x_3351_, 1, v_k_3354_);
lean_ctor_set(v___x_3351_, 0, v___x_3366_);
v___x_3375_ = v___x_3351_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_k_3354_);
lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_v_3355_);
lean_ctor_set(v_reuseFailAlloc_3376_, 3, v___y_3368_);
lean_ctor_set(v_reuseFailAlloc_3376_, 4, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
v___jp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_nat_add(v___x_3365_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec(v___x_3365_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_l_3356_);
lean_ctor_set(v___x_3331_, 3, v_impl_3334_);
lean_ctor_set(v___x_3331_, 0, v___x_3380_);
v___x_3382_ = v___x_3331_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_impl_3334_);
lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_l_3356_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3383_; 
v___x_3383_ = lean_nat_add(v___x_3335_, v_size_3358_);
if (lean_obj_tag(v_r_3357_) == 0)
{
lean_object* v_size_3384_; 
v_size_3384_ = lean_ctor_get(v_r_3357_, 0);
lean_inc(v_size_3384_);
v___y_3368_ = v___x_3382_;
v___y_3369_ = v___x_3383_;
v___y_3370_ = v_size_3384_;
goto v___jp_3367_;
}
else
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_unsigned_to_nat(0u);
v___y_3368_ = v___x_3382_;
v___y_3369_ = v___x_3383_;
v___y_3370_ = v___x_3385_;
goto v___jp_3367_;
}
}
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_del_object(v___x_3331_);
v___x_3395_ = lean_nat_add(v___x_3335_, v_size_3336_);
lean_dec(v_size_3336_);
v___x_3396_ = lean_nat_add(v___x_3395_, v_size_3337_);
lean_dec(v_size_3337_);
v___x_3397_ = lean_nat_add(v___x_3395_, v_size_3353_);
lean_dec(v___x_3395_);
lean_inc_ref(v_impl_3334_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 4, v_l_3340_);
lean_ctor_set(v___x_3351_, 3, v_impl_3334_);
lean_ctor_set(v___x_3351_, 2, v_v_3327_);
lean_ctor_set(v___x_3351_, 1, v_k_3326_);
lean_ctor_set(v___x_3351_, 0, v___x_3397_);
v___x_3399_ = v___x_3351_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3412_, 3, v_impl_3334_);
lean_ctor_set(v_reuseFailAlloc_3412_, 4, v_l_3340_);
v___x_3399_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v_isSharedCheck_3406_ = !lean_is_exclusive(v_impl_3334_);
if (v_isSharedCheck_3406_ == 0)
{
lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3407_ = lean_ctor_get(v_impl_3334_, 4);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_impl_3334_, 3);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_impl_3334_, 2);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_impl_3334_, 1);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_impl_3334_, 0);
lean_dec(v_unused_3411_);
v___x_3401_ = v_impl_3334_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_dec(v_impl_3334_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 4, v_r_3341_);
lean_ctor_set(v___x_3401_, 3, v___x_3399_);
lean_ctor_set(v___x_3401_, 2, v_v_3339_);
lean_ctor_set(v___x_3401_, 1, v_k_3338_);
lean_ctor_set(v___x_3401_, 0, v___x_3396_);
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v_r_3341_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v_size_3419_ = lean_ctor_get(v_impl_3334_, 0);
lean_inc(v_size_3419_);
v___x_3420_ = lean_nat_add(v___x_3335_, v_size_3419_);
lean_dec(v_size_3419_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 3, v_impl_3334_);
lean_ctor_set(v___x_3331_, 0, v___x_3420_);
v___x_3422_ = v___x_3331_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3423_, 3, v_impl_3334_);
lean_ctor_set(v_reuseFailAlloc_3423_, 4, v_r_3329_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
if (lean_obj_tag(v_r_3329_) == 0)
{
lean_object* v_l_3424_; 
v_l_3424_ = lean_ctor_get(v_r_3329_, 3);
lean_inc(v_l_3424_);
if (lean_obj_tag(v_l_3424_) == 0)
{
lean_object* v_r_3425_; 
v_r_3425_ = lean_ctor_get(v_r_3329_, 4);
lean_inc(v_r_3425_);
if (lean_obj_tag(v_r_3425_) == 0)
{
lean_object* v_size_3426_; lean_object* v_k_3427_; lean_object* v_v_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3441_; 
v_size_3426_ = lean_ctor_get(v_r_3329_, 0);
v_k_3427_ = lean_ctor_get(v_r_3329_, 1);
v_v_3428_ = lean_ctor_get(v_r_3329_, 2);
v_isSharedCheck_3441_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3441_ == 0)
{
lean_object* v_unused_3442_; lean_object* v_unused_3443_; 
v_unused_3442_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3443_);
v___x_3430_ = v_r_3329_;
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_v_3428_);
lean_inc(v_k_3427_);
lean_inc(v_size_3426_);
lean_dec(v_r_3329_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3441_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_size_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v_size_3432_ = lean_ctor_get(v_l_3424_, 0);
v___x_3433_ = lean_nat_add(v___x_3335_, v_size_3426_);
lean_dec(v_size_3426_);
v___x_3434_ = lean_nat_add(v___x_3335_, v_size_3432_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 4, v_l_3424_);
lean_ctor_set(v___x_3430_, 3, v_impl_3334_);
lean_ctor_set(v___x_3430_, 2, v_v_3327_);
lean_ctor_set(v___x_3430_, 1, v_k_3326_);
lean_ctor_set(v___x_3430_, 0, v___x_3434_);
v___x_3436_ = v___x_3430_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3434_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3440_, 3, v_impl_3334_);
lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_l_3424_);
v___x_3436_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3438_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_r_3425_);
lean_ctor_set(v___x_3331_, 3, v___x_3436_);
lean_ctor_set(v___x_3331_, 2, v_v_3428_);
lean_ctor_set(v___x_3331_, 1, v_k_3427_);
lean_ctor_set(v___x_3331_, 0, v___x_3433_);
v___x_3438_ = v___x_3331_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_k_3427_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_v_3428_);
lean_ctor_set(v_reuseFailAlloc_3439_, 3, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3439_, 4, v_r_3425_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
else
{
lean_object* v_k_3444_; lean_object* v_v_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3468_; 
v_k_3444_ = lean_ctor_get(v_r_3329_, 1);
v_v_3445_ = lean_ctor_get(v_r_3329_, 2);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; lean_object* v_unused_3470_; lean_object* v_unused_3471_; 
v_unused_3469_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3469_);
v_unused_3470_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3470_);
v_unused_3471_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3471_);
v___x_3447_ = v_r_3329_;
v_isShared_3448_ = v_isSharedCheck_3468_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_v_3445_);
lean_inc(v_k_3444_);
lean_dec(v_r_3329_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3468_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_k_3449_; lean_object* v_v_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3464_; 
v_k_3449_ = lean_ctor_get(v_l_3424_, 1);
v_v_3450_ = lean_ctor_get(v_l_3424_, 2);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_l_3424_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; lean_object* v_unused_3467_; 
v_unused_3465_ = lean_ctor_get(v_l_3424_, 4);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_l_3424_, 3);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_l_3424_, 0);
lean_dec(v_unused_3467_);
v___x_3452_ = v_l_3424_;
v_isShared_3453_ = v_isSharedCheck_3464_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_v_3450_);
lean_inc(v_k_3449_);
lean_dec(v_l_3424_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3464_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3454_ = lean_unsigned_to_nat(3u);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 4, v_r_3425_);
lean_ctor_set(v___x_3452_, 3, v_r_3425_);
lean_ctor_set(v___x_3452_, 2, v_v_3327_);
lean_ctor_set(v___x_3452_, 1, v_k_3326_);
lean_ctor_set(v___x_3452_, 0, v___x_3335_);
v___x_3456_ = v___x_3452_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_r_3425_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_r_3425_);
v___x_3456_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3458_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 3, v_r_3425_);
lean_ctor_set(v___x_3447_, 0, v___x_3335_);
v___x_3458_ = v___x_3447_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_k_3444_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_v_3445_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_r_3425_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_r_3425_);
v___x_3458_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3458_);
lean_ctor_set(v___x_3331_, 3, v___x_3456_);
lean_ctor_set(v___x_3331_, 2, v_v_3450_);
lean_ctor_set(v___x_3331_, 1, v_k_3449_);
lean_ctor_set(v___x_3331_, 0, v___x_3454_);
v___x_3460_ = v___x_3331_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3449_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3450_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3472_; 
v_r_3472_ = lean_ctor_get(v_r_3329_, 4);
lean_inc(v_r_3472_);
if (lean_obj_tag(v_r_3472_) == 0)
{
lean_object* v_k_3473_; lean_object* v_v_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3485_; 
v_k_3473_ = lean_ctor_get(v_r_3329_, 1);
v_v_3474_ = lean_ctor_get(v_r_3329_, 2);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; lean_object* v_unused_3487_; lean_object* v_unused_3488_; 
v_unused_3486_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3486_);
v_unused_3487_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3487_);
v_unused_3488_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3488_);
v___x_3476_ = v_r_3329_;
v_isShared_3477_ = v_isSharedCheck_3485_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_v_3474_);
lean_inc(v_k_3473_);
lean_dec(v_r_3329_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3485_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3478_ = lean_unsigned_to_nat(3u);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 4, v_l_3424_);
lean_ctor_set(v___x_3476_, 2, v_v_3327_);
lean_ctor_set(v___x_3476_, 1, v_k_3326_);
lean_ctor_set(v___x_3476_, 0, v___x_3335_);
v___x_3480_ = v___x_3476_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_l_3424_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_l_3424_);
v___x_3480_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3482_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_r_3472_);
lean_ctor_set(v___x_3331_, 3, v___x_3480_);
lean_ctor_set(v___x_3331_, 2, v_v_3474_);
lean_ctor_set(v___x_3331_, 1, v_k_3473_);
lean_ctor_set(v___x_3331_, 0, v___x_3478_);
v___x_3482_ = v___x_3331_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_k_3473_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v_v_3474_);
lean_ctor_set(v_reuseFailAlloc_3483_, 3, v___x_3480_);
lean_ctor_set(v_reuseFailAlloc_3483_, 4, v_r_3472_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_size_3489_; lean_object* v_k_3490_; lean_object* v_v_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3502_; 
v_size_3489_ = lean_ctor_get(v_r_3329_, 0);
v_k_3490_ = lean_ctor_get(v_r_3329_, 1);
v_v_3491_ = lean_ctor_get(v_r_3329_, 2);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; lean_object* v_unused_3504_; 
v_unused_3503_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3504_);
v___x_3493_ = v_r_3329_;
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_v_3491_);
lean_inc(v_k_3490_);
lean_inc(v_size_3489_);
lean_dec(v_r_3329_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 3, v_r_3472_);
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_size_3489_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_k_3490_);
lean_ctor_set(v_reuseFailAlloc_3501_, 2, v_v_3491_);
lean_ctor_set(v_reuseFailAlloc_3501_, 3, v_r_3472_);
lean_ctor_set(v_reuseFailAlloc_3501_, 4, v_r_3472_);
v___x_3496_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3497_ = lean_unsigned_to_nat(2u);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3496_);
lean_ctor_set(v___x_3331_, 3, v_r_3472_);
lean_ctor_set(v___x_3331_, 0, v___x_3497_);
v___x_3499_ = v___x_3331_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3500_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3500_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3500_, 3, v_r_3472_);
lean_ctor_set(v_reuseFailAlloc_3500_, 4, v___x_3496_);
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
}
else
{
lean_object* v___x_3506_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 3, v_r_3329_);
lean_ctor_set(v___x_3331_, 0, v___x_3335_);
v___x_3506_ = v___x_3331_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_r_3329_);
lean_ctor_set(v_reuseFailAlloc_3507_, 4, v_r_3329_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
case 1:
{
lean_del_object(v___x_3331_);
lean_dec(v_v_3327_);
lean_dec(v_k_3326_);
if (lean_obj_tag(v_l_3328_) == 0)
{
if (lean_obj_tag(v_r_3329_) == 0)
{
lean_object* v_size_3508_; lean_object* v_k_3509_; lean_object* v_v_3510_; lean_object* v_l_3511_; lean_object* v_r_3512_; lean_object* v_size_3513_; lean_object* v_k_3514_; lean_object* v_v_3515_; lean_object* v_l_3516_; lean_object* v_r_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; 
v_size_3508_ = lean_ctor_get(v_l_3328_, 0);
v_k_3509_ = lean_ctor_get(v_l_3328_, 1);
v_v_3510_ = lean_ctor_get(v_l_3328_, 2);
v_l_3511_ = lean_ctor_get(v_l_3328_, 3);
v_r_3512_ = lean_ctor_get(v_l_3328_, 4);
lean_inc(v_r_3512_);
v_size_3513_ = lean_ctor_get(v_r_3329_, 0);
v_k_3514_ = lean_ctor_get(v_r_3329_, 1);
v_v_3515_ = lean_ctor_get(v_r_3329_, 2);
v_l_3516_ = lean_ctor_get(v_r_3329_, 3);
lean_inc(v_l_3516_);
v_r_3517_ = lean_ctor_get(v_r_3329_, 4);
v___x_3518_ = lean_unsigned_to_nat(1u);
v___x_3519_ = lean_nat_dec_lt(v_size_3508_, v_size_3513_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3655_; 
lean_inc(v_l_3511_);
lean_inc(v_v_3510_);
lean_inc(v_k_3509_);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; lean_object* v_unused_3657_; lean_object* v_unused_3658_; lean_object* v_unused_3659_; lean_object* v_unused_3660_; 
v_unused_3656_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3656_);
v_unused_3657_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3657_);
v_unused_3658_ = lean_ctor_get(v_l_3328_, 2);
lean_dec(v_unused_3658_);
v_unused_3659_ = lean_ctor_get(v_l_3328_, 1);
lean_dec(v_unused_3659_);
v_unused_3660_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3660_);
v___x_3521_ = v_l_3328_;
v_isShared_3522_ = v_isSharedCheck_3655_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v_l_3328_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3655_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v_tree_3524_; 
v___x_3523_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3509_, v_v_3510_, v_l_3511_, v_r_3512_);
v_tree_3524_ = lean_ctor_get(v___x_3523_, 2);
lean_inc(v_tree_3524_);
if (lean_obj_tag(v_tree_3524_) == 0)
{
lean_object* v_k_3525_; lean_object* v_v_3526_; lean_object* v_size_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_k_3525_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_k_3525_);
v_v_3526_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_v_3526_);
lean_dec_ref(v___x_3523_);
v_size_3527_ = lean_ctor_get(v_tree_3524_, 0);
v___x_3528_ = lean_unsigned_to_nat(3u);
v___x_3529_ = lean_nat_mul(v___x_3528_, v_size_3527_);
v___x_3530_ = lean_nat_dec_lt(v___x_3529_, v_size_3513_);
lean_dec(v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
lean_dec(v_l_3516_);
v___x_3531_ = lean_nat_add(v___x_3518_, v_size_3527_);
v___x_3532_ = lean_nat_add(v___x_3531_, v_size_3513_);
lean_dec(v___x_3531_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v_r_3329_);
lean_ctor_set(v___x_3521_, 3, v_tree_3524_);
lean_ctor_set(v___x_3521_, 2, v_v_3526_);
lean_ctor_set(v___x_3521_, 1, v_k_3525_);
lean_ctor_set(v___x_3521_, 0, v___x_3532_);
v___x_3534_ = v___x_3521_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_tree_3524_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_r_3329_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
else
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3590_; 
lean_inc(v_r_3517_);
lean_inc(v_v_3515_);
lean_inc(v_k_3514_);
lean_inc(v_size_3513_);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; lean_object* v_unused_3592_; lean_object* v_unused_3593_; lean_object* v_unused_3594_; lean_object* v_unused_3595_; 
v_unused_3591_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3591_);
v_unused_3592_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3592_);
v_unused_3593_ = lean_ctor_get(v_r_3329_, 2);
lean_dec(v_unused_3593_);
v_unused_3594_ = lean_ctor_get(v_r_3329_, 1);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3595_);
v___x_3537_ = v_r_3329_;
v_isShared_3538_ = v_isSharedCheck_3590_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v_r_3329_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3590_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v_size_3539_; lean_object* v_k_3540_; lean_object* v_v_3541_; lean_object* v_l_3542_; lean_object* v_r_3543_; lean_object* v_size_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_size_3539_ = lean_ctor_get(v_l_3516_, 0);
v_k_3540_ = lean_ctor_get(v_l_3516_, 1);
v_v_3541_ = lean_ctor_get(v_l_3516_, 2);
v_l_3542_ = lean_ctor_get(v_l_3516_, 3);
v_r_3543_ = lean_ctor_get(v_l_3516_, 4);
v_size_3544_ = lean_ctor_get(v_r_3517_, 0);
v___x_3545_ = lean_unsigned_to_nat(2u);
v___x_3546_ = lean_nat_mul(v___x_3545_, v_size_3544_);
v___x_3547_ = lean_nat_dec_lt(v_size_3539_, v___x_3546_);
lean_dec(v___x_3546_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3575_; 
lean_inc(v_r_3543_);
lean_inc(v_l_3542_);
lean_inc(v_v_3541_);
lean_inc(v_k_3540_);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_l_3516_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; 
v_unused_3576_ = lean_ctor_get(v_l_3516_, 4);
lean_dec(v_unused_3576_);
v_unused_3577_ = lean_ctor_get(v_l_3516_, 3);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_l_3516_, 2);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_l_3516_, 1);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_l_3516_, 0);
lean_dec(v_unused_3580_);
v___x_3549_ = v_l_3516_;
v_isShared_3550_ = v_isSharedCheck_3575_;
goto v_resetjp_3548_;
}
else
{
lean_dec(v_l_3516_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3575_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3565_; 
v___x_3551_ = lean_nat_add(v___x_3518_, v_size_3527_);
v___x_3552_ = lean_nat_add(v___x_3551_, v_size_3513_);
lean_dec(v_size_3513_);
if (lean_obj_tag(v_l_3542_) == 0)
{
lean_object* v_size_3573_; 
v_size_3573_ = lean_ctor_get(v_l_3542_, 0);
lean_inc(v_size_3573_);
v___y_3565_ = v_size_3573_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_unsigned_to_nat(0u);
v___y_3565_ = v___x_3574_;
goto v___jp_3564_;
}
v___jp_3553_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_nat_add(v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec(v___y_3555_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 4, v_r_3517_);
lean_ctor_set(v___x_3549_, 3, v_r_3543_);
lean_ctor_set(v___x_3549_, 2, v_v_3515_);
lean_ctor_set(v___x_3549_, 1, v_k_3514_);
lean_ctor_set(v___x_3549_, 0, v___x_3557_);
v___x_3559_ = v___x_3549_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v_r_3543_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v_r_3517_);
v___x_3559_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3561_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 4, v___x_3559_);
lean_ctor_set(v___x_3537_, 3, v___y_3554_);
lean_ctor_set(v___x_3537_, 2, v_v_3541_);
lean_ctor_set(v___x_3537_, 1, v_k_3540_);
lean_ctor_set(v___x_3537_, 0, v___x_3552_);
v___x_3561_ = v___x_3537_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_k_3540_);
lean_ctor_set(v_reuseFailAlloc_3562_, 2, v_v_3541_);
lean_ctor_set(v_reuseFailAlloc_3562_, 3, v___y_3554_);
lean_ctor_set(v_reuseFailAlloc_3562_, 4, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
v___jp_3564_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = lean_nat_add(v___x_3551_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec(v___x_3551_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v_l_3542_);
lean_ctor_set(v___x_3521_, 3, v_tree_3524_);
lean_ctor_set(v___x_3521_, 2, v_v_3526_);
lean_ctor_set(v___x_3521_, 1, v_k_3525_);
lean_ctor_set(v___x_3521_, 0, v___x_3566_);
v___x_3568_ = v___x_3521_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3572_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3572_, 3, v_tree_3524_);
lean_ctor_set(v_reuseFailAlloc_3572_, 4, v_l_3542_);
v___x_3568_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_nat_add(v___x_3518_, v_size_3544_);
if (lean_obj_tag(v_r_3543_) == 0)
{
lean_object* v_size_3570_; 
v_size_3570_ = lean_ctor_get(v_r_3543_, 0);
lean_inc(v_size_3570_);
v___y_3554_ = v___x_3568_;
v___y_3555_ = v___x_3569_;
v___y_3556_ = v_size_3570_;
goto v___jp_3553_;
}
else
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_unsigned_to_nat(0u);
v___y_3554_ = v___x_3568_;
v___y_3555_ = v___x_3569_;
v___y_3556_ = v___x_3571_;
goto v___jp_3553_;
}
}
}
}
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3581_ = lean_nat_add(v___x_3518_, v_size_3527_);
v___x_3582_ = lean_nat_add(v___x_3581_, v_size_3513_);
lean_dec(v_size_3513_);
v___x_3583_ = lean_nat_add(v___x_3581_, v_size_3539_);
lean_dec(v___x_3581_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 4, v_l_3516_);
lean_ctor_set(v___x_3537_, 3, v_tree_3524_);
lean_ctor_set(v___x_3537_, 2, v_v_3526_);
lean_ctor_set(v___x_3537_, 1, v_k_3525_);
lean_ctor_set(v___x_3537_, 0, v___x_3583_);
v___x_3585_ = v___x_3537_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3583_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3589_, 3, v_tree_3524_);
lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_l_3516_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3587_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v_r_3517_);
lean_ctor_set(v___x_3521_, 3, v___x_3585_);
lean_ctor_set(v___x_3521_, 2, v_v_3515_);
lean_ctor_set(v___x_3521_, 1, v_k_3514_);
lean_ctor_set(v___x_3521_, 0, v___x_3582_);
v___x_3587_ = v___x_3521_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v___x_3585_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_r_3517_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3649_; 
lean_inc(v_r_3517_);
lean_inc(v_v_3515_);
lean_inc(v_k_3514_);
lean_inc(v_size_3513_);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; lean_object* v_unused_3651_; lean_object* v_unused_3652_; lean_object* v_unused_3653_; lean_object* v_unused_3654_; 
v_unused_3650_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3650_);
v_unused_3651_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v_r_3329_, 2);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_r_3329_, 1);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3654_);
v___x_3597_ = v_r_3329_;
v_isShared_3598_ = v_isSharedCheck_3649_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v_r_3329_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3649_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
if (lean_obj_tag(v_l_3516_) == 0)
{
if (lean_obj_tag(v_r_3517_) == 0)
{
lean_object* v_k_3599_; lean_object* v_v_3600_; lean_object* v_size_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v_k_3599_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_k_3599_);
v_v_3600_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_v_3600_);
lean_dec_ref(v___x_3523_);
v_size_3601_ = lean_ctor_get(v_l_3516_, 0);
v___x_3602_ = lean_nat_add(v___x_3518_, v_size_3513_);
lean_dec(v_size_3513_);
v___x_3603_ = lean_nat_add(v___x_3518_, v_size_3601_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 4, v_l_3516_);
lean_ctor_set(v___x_3597_, 3, v_tree_3524_);
lean_ctor_set(v___x_3597_, 2, v_v_3600_);
lean_ctor_set(v___x_3597_, 1, v_k_3599_);
lean_ctor_set(v___x_3597_, 0, v___x_3603_);
v___x_3605_ = v___x_3597_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_k_3599_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_v_3600_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_tree_3524_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v_l_3516_);
v___x_3605_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v_r_3517_);
lean_ctor_set(v___x_3521_, 3, v___x_3605_);
lean_ctor_set(v___x_3521_, 2, v_v_3515_);
lean_ctor_set(v___x_3521_, 1, v_k_3514_);
lean_ctor_set(v___x_3521_, 0, v___x_3602_);
v___x_3607_ = v___x_3521_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3608_, 3, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3608_, 4, v_r_3517_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v_k_3610_; lean_object* v_v_3611_; lean_object* v_k_3612_; lean_object* v_v_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_size_3513_);
v_k_3610_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_k_3610_);
v_v_3611_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_v_3611_);
lean_dec_ref(v___x_3523_);
v_k_3612_ = lean_ctor_get(v_l_3516_, 1);
v_v_3613_ = lean_ctor_get(v_l_3516_, 2);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_l_3516_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3628_ = lean_ctor_get(v_l_3516_, 4);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_l_3516_, 3);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_l_3516_, 0);
lean_dec(v_unused_3630_);
v___x_3615_ = v_l_3516_;
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_v_3613_);
lean_inc(v_k_3612_);
lean_dec(v_l_3516_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3627_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_unsigned_to_nat(3u);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 4, v_r_3517_);
lean_ctor_set(v___x_3615_, 3, v_r_3517_);
lean_ctor_set(v___x_3615_, 2, v_v_3611_);
lean_ctor_set(v___x_3615_, 1, v_k_3610_);
lean_ctor_set(v___x_3615_, 0, v___x_3518_);
v___x_3619_ = v___x_3615_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v_k_3610_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v_v_3611_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v_r_3517_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v_r_3517_);
v___x_3619_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 3, v_r_3517_);
lean_ctor_set(v___x_3597_, 0, v___x_3518_);
v___x_3621_ = v___x_3597_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_r_3517_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_r_3517_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v___x_3621_);
lean_ctor_set(v___x_3521_, 3, v___x_3619_);
lean_ctor_set(v___x_3521_, 2, v_v_3613_);
lean_ctor_set(v___x_3521_, 1, v_k_3612_);
lean_ctor_set(v___x_3521_, 0, v___x_3617_);
v___x_3623_ = v___x_3521_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_k_3612_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_v_3613_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3517_) == 0)
{
lean_object* v_k_3631_; lean_object* v_v_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_dec(v_size_3513_);
v_k_3631_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_k_3631_);
v_v_3632_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_v_3632_);
lean_dec_ref(v___x_3523_);
v___x_3633_ = lean_unsigned_to_nat(3u);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 4, v_l_3516_);
lean_ctor_set(v___x_3597_, 2, v_v_3632_);
lean_ctor_set(v___x_3597_, 1, v_k_3631_);
lean_ctor_set(v___x_3597_, 0, v___x_3518_);
v___x_3635_ = v___x_3597_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_l_3516_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_l_3516_);
v___x_3635_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3637_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v_r_3517_);
lean_ctor_set(v___x_3521_, 3, v___x_3635_);
lean_ctor_set(v___x_3521_, 2, v_v_3515_);
lean_ctor_set(v___x_3521_, 1, v_k_3514_);
lean_ctor_set(v___x_3521_, 0, v___x_3633_);
v___x_3637_ = v___x_3521_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v___x_3635_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v_r_3517_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
else
{
lean_object* v_k_3640_; lean_object* v_v_3641_; lean_object* v___x_3643_; 
v_k_3640_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_k_3640_);
v_v_3641_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_v_3641_);
lean_dec_ref(v___x_3523_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 3, v_r_3517_);
v___x_3643_ = v___x_3597_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_size_3513_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3514_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3515_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_r_3517_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_r_3517_);
v___x_3643_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_unsigned_to_nat(2u);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 4, v___x_3643_);
lean_ctor_set(v___x_3521_, 3, v_r_3517_);
lean_ctor_set(v___x_3521_, 2, v_v_3641_);
lean_ctor_set(v___x_3521_, 1, v_k_3640_);
lean_ctor_set(v___x_3521_, 0, v___x_3644_);
v___x_3646_ = v___x_3521_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_k_3640_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v_v_3641_);
lean_ctor_set(v_reuseFailAlloc_3647_, 3, v_r_3517_);
lean_ctor_set(v_reuseFailAlloc_3647_, 4, v___x_3643_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
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
lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3813_; 
lean_inc(v_r_3517_);
lean_inc(v_v_3515_);
lean_inc(v_k_3514_);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_r_3329_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3814_ = lean_ctor_get(v_r_3329_, 4);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_r_3329_, 3);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_r_3329_, 2);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_r_3329_, 1);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_r_3329_, 0);
lean_dec(v_unused_3818_);
v___x_3662_ = v_r_3329_;
v_isShared_3663_ = v_isSharedCheck_3813_;
goto v_resetjp_3661_;
}
else
{
lean_dec(v_r_3329_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3813_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v_tree_3665_; 
v___x_3664_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3514_, v_v_3515_, v_l_3516_, v_r_3517_);
v_tree_3665_ = lean_ctor_get(v___x_3664_, 2);
lean_inc(v_tree_3665_);
if (lean_obj_tag(v_tree_3665_) == 0)
{
lean_object* v_k_3666_; lean_object* v_v_3667_; lean_object* v_size_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_k_3666_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_k_3666_);
v_v_3667_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_v_3667_);
lean_dec_ref(v___x_3664_);
v_size_3668_ = lean_ctor_get(v_tree_3665_, 0);
v___x_3669_ = lean_unsigned_to_nat(3u);
v___x_3670_ = lean_nat_mul(v___x_3669_, v_size_3668_);
v___x_3671_ = lean_nat_dec_lt(v___x_3670_, v_size_3508_);
lean_dec(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
lean_dec(v_r_3512_);
v___x_3672_ = lean_nat_add(v___x_3518_, v_size_3508_);
v___x_3673_ = lean_nat_add(v___x_3672_, v_size_3668_);
lean_dec(v___x_3672_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_tree_3665_);
lean_ctor_set(v___x_3662_, 3, v_l_3328_);
lean_ctor_set(v___x_3662_, 2, v_v_3667_);
lean_ctor_set(v___x_3662_, 1, v_k_3666_);
lean_ctor_set(v___x_3662_, 0, v___x_3673_);
v___x_3675_ = v___x_3662_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3666_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3667_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_tree_3665_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
else
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3742_; 
lean_inc(v_l_3511_);
lean_inc(v_v_3510_);
lean_inc(v_k_3509_);
lean_inc(v_size_3508_);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; 
v_unused_3743_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_l_3328_, 2);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_l_3328_, 1);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3747_);
v___x_3678_ = v_l_3328_;
v_isShared_3679_ = v_isSharedCheck_3742_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v_l_3328_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3742_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_size_3680_; lean_object* v_size_3681_; lean_object* v_k_3682_; lean_object* v_v_3683_; lean_object* v_l_3684_; lean_object* v_r_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_size_3680_ = lean_ctor_get(v_l_3511_, 0);
v_size_3681_ = lean_ctor_get(v_r_3512_, 0);
v_k_3682_ = lean_ctor_get(v_r_3512_, 1);
v_v_3683_ = lean_ctor_get(v_r_3512_, 2);
v_l_3684_ = lean_ctor_get(v_r_3512_, 3);
v_r_3685_ = lean_ctor_get(v_r_3512_, 4);
v___x_3686_ = lean_unsigned_to_nat(2u);
v___x_3687_ = lean_nat_mul(v___x_3686_, v_size_3680_);
v___x_3688_ = lean_nat_dec_lt(v_size_3681_, v___x_3687_);
lean_dec(v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3726_; 
lean_inc(v_r_3685_);
lean_inc(v_l_3684_);
lean_inc(v_v_3683_);
lean_inc(v_k_3682_);
lean_del_object(v___x_3678_);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_r_3512_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; 
v_unused_3727_ = lean_ctor_get(v_r_3512_, 4);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_r_3512_, 3);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_r_3512_, 2);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_r_3512_, 1);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_r_3512_, 0);
lean_dec(v_unused_3731_);
v___x_3690_ = v_r_3512_;
v_isShared_3691_ = v_isSharedCheck_3726_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v_r_3512_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3726_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___x_3714_; lean_object* v___y_3716_; 
v___x_3692_ = lean_nat_add(v___x_3518_, v_size_3508_);
lean_dec(v_size_3508_);
v___x_3693_ = lean_nat_add(v___x_3692_, v_size_3668_);
lean_dec(v___x_3692_);
v___x_3714_ = lean_nat_add(v___x_3518_, v_size_3680_);
if (lean_obj_tag(v_l_3684_) == 0)
{
lean_object* v_size_3724_; 
v_size_3724_ = lean_ctor_get(v_l_3684_, 0);
lean_inc(v_size_3724_);
v___y_3716_ = v_size_3724_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_unsigned_to_nat(0u);
v___y_3716_ = v___x_3725_;
goto v___jp_3715_;
}
v___jp_3694_:
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = lean_nat_add(v___y_3695_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec(v___y_3695_);
lean_inc_ref(v_tree_3665_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 4, v_tree_3665_);
lean_ctor_set(v___x_3690_, 3, v_r_3685_);
lean_ctor_set(v___x_3690_, 2, v_v_3667_);
lean_ctor_set(v___x_3690_, 1, v_k_3666_);
lean_ctor_set(v___x_3690_, 0, v___x_3698_);
v___x_3700_ = v___x_3690_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3666_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3667_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_r_3685_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_tree_3665_);
v___x_3700_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_isSharedCheck_3707_ = !lean_is_exclusive(v_tree_3665_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; 
v_unused_3708_ = lean_ctor_get(v_tree_3665_, 4);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_tree_3665_, 3);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_tree_3665_, 2);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_tree_3665_, 1);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_tree_3665_, 0);
lean_dec(v_unused_3712_);
v___x_3702_ = v_tree_3665_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_tree_3665_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 4, v___x_3700_);
lean_ctor_set(v___x_3702_, 3, v___y_3696_);
lean_ctor_set(v___x_3702_, 2, v_v_3683_);
lean_ctor_set(v___x_3702_, 1, v_k_3682_);
lean_ctor_set(v___x_3702_, 0, v___x_3693_);
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_k_3682_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_v_3683_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v___y_3696_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v___x_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
v___jp_3715_:
{
lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3717_ = lean_nat_add(v___x_3714_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec(v___x_3714_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_l_3684_);
lean_ctor_set(v___x_3662_, 3, v_l_3511_);
lean_ctor_set(v___x_3662_, 2, v_v_3510_);
lean_ctor_set(v___x_3662_, 1, v_k_3509_);
lean_ctor_set(v___x_3662_, 0, v___x_3717_);
v___x_3719_ = v___x_3662_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_l_3684_);
v___x_3719_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_nat_add(v___x_3518_, v_size_3668_);
if (lean_obj_tag(v_r_3685_) == 0)
{
lean_object* v_size_3721_; 
v_size_3721_ = lean_ctor_get(v_r_3685_, 0);
lean_inc(v_size_3721_);
v___y_3695_ = v___x_3720_;
v___y_3696_ = v___x_3719_;
v___y_3697_ = v_size_3721_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_unsigned_to_nat(0u);
v___y_3695_ = v___x_3720_;
v___y_3696_ = v___x_3719_;
v___y_3697_ = v___x_3722_;
goto v___jp_3694_;
}
}
}
}
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3732_ = lean_nat_add(v___x_3518_, v_size_3508_);
lean_dec(v_size_3508_);
v___x_3733_ = lean_nat_add(v___x_3732_, v_size_3668_);
lean_dec(v___x_3732_);
v___x_3734_ = lean_nat_add(v___x_3518_, v_size_3668_);
v___x_3735_ = lean_nat_add(v___x_3734_, v_size_3681_);
lean_dec(v___x_3734_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_tree_3665_);
lean_ctor_set(v___x_3662_, 3, v_r_3512_);
lean_ctor_set(v___x_3662_, 2, v_v_3667_);
lean_ctor_set(v___x_3662_, 1, v_k_3666_);
lean_ctor_set(v___x_3662_, 0, v___x_3735_);
v___x_3737_ = v___x_3662_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3666_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3667_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_r_3512_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_tree_3665_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 4, v___x_3737_);
lean_ctor_set(v___x_3678_, 0, v___x_3733_);
v___x_3739_ = v___x_3678_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3511_) == 0)
{
lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3771_; 
lean_inc_ref(v_l_3511_);
lean_inc(v_v_3510_);
lean_inc(v_k_3509_);
lean_inc(v_size_3508_);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3771_ == 0)
{
lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; lean_object* v_unused_3775_; lean_object* v_unused_3776_; 
v_unused_3772_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_l_3328_, 2);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_l_3328_, 1);
lean_dec(v_unused_3775_);
v_unused_3776_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3776_);
v___x_3749_ = v_l_3328_;
v_isShared_3750_ = v_isSharedCheck_3771_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v_l_3328_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3771_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
if (lean_obj_tag(v_r_3512_) == 0)
{
lean_object* v_k_3751_; lean_object* v_v_3752_; lean_object* v_size_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
v_k_3751_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_k_3751_);
v_v_3752_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_v_3752_);
lean_dec_ref(v___x_3664_);
v_size_3753_ = lean_ctor_get(v_r_3512_, 0);
v___x_3754_ = lean_nat_add(v___x_3518_, v_size_3508_);
lean_dec(v_size_3508_);
v___x_3755_ = lean_nat_add(v___x_3518_, v_size_3753_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_tree_3665_);
lean_ctor_set(v___x_3662_, 3, v_r_3512_);
lean_ctor_set(v___x_3662_, 2, v_v_3752_);
lean_ctor_set(v___x_3662_, 1, v_k_3751_);
lean_ctor_set(v___x_3662_, 0, v___x_3755_);
v___x_3757_ = v___x_3662_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3751_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3752_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_r_3512_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_tree_3665_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 4, v___x_3757_);
lean_ctor_set(v___x_3749_, 0, v___x_3754_);
v___x_3759_ = v___x_3749_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
else
{
lean_object* v_k_3762_; lean_object* v_v_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec(v_size_3508_);
v_k_3762_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_k_3762_);
v_v_3763_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_v_3763_);
lean_dec_ref(v___x_3664_);
v___x_3764_ = lean_unsigned_to_nat(3u);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_3512_);
lean_ctor_set(v___x_3662_, 3, v_r_3512_);
lean_ctor_set(v___x_3662_, 2, v_v_3763_);
lean_ctor_set(v___x_3662_, 1, v_k_3762_);
lean_ctor_set(v___x_3662_, 0, v___x_3518_);
v___x_3766_ = v___x_3662_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_k_3762_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_v_3763_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_r_3512_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_r_3512_);
v___x_3766_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 4, v___x_3766_);
lean_ctor_set(v___x_3749_, 0, v___x_3764_);
v___x_3768_ = v___x_3749_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3769_, 4, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3512_) == 0)
{
lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3801_; 
lean_inc(v_l_3511_);
lean_inc(v_v_3510_);
lean_inc(v_k_3509_);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; lean_object* v_unused_3805_; lean_object* v_unused_3806_; 
v_unused_3802_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_l_3328_, 2);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_l_3328_, 1);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3806_);
v___x_3778_ = v_l_3328_;
v_isShared_3779_ = v_isSharedCheck_3801_;
goto v_resetjp_3777_;
}
else
{
lean_dec(v_l_3328_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3801_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v_k_3782_; lean_object* v_v_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3797_; 
v_k_3780_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_k_3780_);
v_v_3781_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_v_3781_);
lean_dec_ref(v___x_3664_);
v_k_3782_ = lean_ctor_get(v_r_3512_, 1);
v_v_3783_ = lean_ctor_get(v_r_3512_, 2);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_r_3512_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; lean_object* v_unused_3799_; lean_object* v_unused_3800_; 
v_unused_3798_ = lean_ctor_get(v_r_3512_, 4);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_r_3512_, 3);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_r_3512_, 0);
lean_dec(v_unused_3800_);
v___x_3785_ = v_r_3512_;
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_v_3783_);
lean_inc(v_k_3782_);
lean_dec(v_r_3512_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_unsigned_to_nat(3u);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 4, v_l_3511_);
lean_ctor_set(v___x_3785_, 3, v_l_3511_);
lean_ctor_set(v___x_3785_, 2, v_v_3510_);
lean_ctor_set(v___x_3785_, 1, v_k_3509_);
lean_ctor_set(v___x_3785_, 0, v___x_3518_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_l_3511_);
v___x_3789_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_l_3511_);
lean_ctor_set(v___x_3662_, 3, v_l_3511_);
lean_ctor_set(v___x_3662_, 2, v_v_3781_);
lean_ctor_set(v___x_3662_, 1, v_k_3780_);
lean_ctor_set(v___x_3662_, 0, v___x_3518_);
v___x_3791_ = v___x_3662_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_l_3511_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_l_3511_);
v___x_3791_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 4, v___x_3791_);
lean_ctor_set(v___x_3778_, 3, v___x_3789_);
lean_ctor_set(v___x_3778_, 2, v_v_3783_);
lean_ctor_set(v___x_3778_, 1, v_k_3782_);
lean_ctor_set(v___x_3778_, 0, v___x_3787_);
v___x_3793_ = v___x_3778_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
else
{
lean_object* v_k_3807_; lean_object* v_v_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
v_k_3807_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_k_3807_);
v_v_3808_ = lean_ctor_get(v___x_3664_, 1);
lean_inc(v_v_3808_);
lean_dec_ref(v___x_3664_);
v___x_3809_ = lean_unsigned_to_nat(2u);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 4, v_r_3512_);
lean_ctor_set(v___x_3662_, 3, v_l_3328_);
lean_ctor_set(v___x_3662_, 2, v_v_3808_);
lean_ctor_set(v___x_3662_, 1, v_k_3807_);
lean_ctor_set(v___x_3662_, 0, v___x_3809_);
v___x_3811_ = v___x_3662_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_k_3807_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_v_3808_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_r_3512_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
else
{
return v_l_3328_;
}
}
else
{
return v_r_3329_;
}
}
default: 
{
lean_object* v_impl_3819_; lean_object* v___x_3820_; 
v_impl_3819_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3324_, v_r_3329_);
v___x_3820_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3819_) == 0)
{
if (lean_obj_tag(v_l_3328_) == 0)
{
lean_object* v_size_3821_; lean_object* v_size_3822_; lean_object* v_k_3823_; lean_object* v_v_3824_; lean_object* v_l_3825_; lean_object* v_r_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_size_3821_ = lean_ctor_get(v_impl_3819_, 0);
lean_inc(v_size_3821_);
v_size_3822_ = lean_ctor_get(v_l_3328_, 0);
v_k_3823_ = lean_ctor_get(v_l_3328_, 1);
v_v_3824_ = lean_ctor_get(v_l_3328_, 2);
v_l_3825_ = lean_ctor_get(v_l_3328_, 3);
v_r_3826_ = lean_ctor_get(v_l_3328_, 4);
lean_inc(v_r_3826_);
v___x_3827_ = lean_unsigned_to_nat(3u);
v___x_3828_ = lean_nat_mul(v___x_3827_, v_size_3821_);
v___x_3829_ = lean_nat_dec_lt(v___x_3828_, v_size_3822_);
lean_dec(v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec(v_r_3826_);
v___x_3830_ = lean_nat_add(v___x_3820_, v_size_3822_);
v___x_3831_ = lean_nat_add(v___x_3830_, v_size_3821_);
lean_dec(v_size_3821_);
lean_dec(v___x_3830_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_impl_3819_);
lean_ctor_set(v___x_3331_, 0, v___x_3831_);
v___x_3833_ = v___x_3331_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3834_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3834_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3834_, 4, v_impl_3819_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
else
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3900_; 
lean_inc(v_l_3825_);
lean_inc(v_v_3824_);
lean_inc(v_k_3823_);
lean_inc(v_size_3822_);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; 
v_unused_3901_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_l_3328_, 2);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_l_3328_, 1);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3905_);
v___x_3836_ = v_l_3328_;
v_isShared_3837_ = v_isSharedCheck_3900_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v_l_3328_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3900_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_size_3838_; lean_object* v_size_3839_; lean_object* v_k_3840_; lean_object* v_v_3841_; lean_object* v_l_3842_; lean_object* v_r_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_size_3838_ = lean_ctor_get(v_l_3825_, 0);
v_size_3839_ = lean_ctor_get(v_r_3826_, 0);
v_k_3840_ = lean_ctor_get(v_r_3826_, 1);
v_v_3841_ = lean_ctor_get(v_r_3826_, 2);
v_l_3842_ = lean_ctor_get(v_r_3826_, 3);
v_r_3843_ = lean_ctor_get(v_r_3826_, 4);
v___x_3844_ = lean_unsigned_to_nat(2u);
v___x_3845_ = lean_nat_mul(v___x_3844_, v_size_3838_);
v___x_3846_ = lean_nat_dec_lt(v_size_3839_, v___x_3845_);
lean_dec(v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3875_; 
lean_inc(v_r_3843_);
lean_inc(v_l_3842_);
lean_inc(v_v_3841_);
lean_inc(v_k_3840_);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_r_3826_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3876_ = lean_ctor_get(v_r_3826_, 4);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_r_3826_, 3);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_r_3826_, 2);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_r_3826_, 1);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_r_3826_, 0);
lean_dec(v_unused_3880_);
v___x_3848_ = v_r_3826_;
v_isShared_3849_ = v_isSharedCheck_3875_;
goto v_resetjp_3847_;
}
else
{
lean_dec(v_r_3826_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3875_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___x_3863_; lean_object* v___y_3865_; 
v___x_3850_ = lean_nat_add(v___x_3820_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3851_ = lean_nat_add(v___x_3850_, v_size_3821_);
lean_dec(v___x_3850_);
v___x_3863_ = lean_nat_add(v___x_3820_, v_size_3838_);
if (lean_obj_tag(v_l_3842_) == 0)
{
lean_object* v_size_3873_; 
v_size_3873_ = lean_ctor_get(v_l_3842_, 0);
lean_inc(v_size_3873_);
v___y_3865_ = v_size_3873_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_unsigned_to_nat(0u);
v___y_3865_ = v___x_3874_;
goto v___jp_3864_;
}
v___jp_3852_:
{
lean_object* v___x_3856_; lean_object* v___x_3858_; 
v___x_3856_ = lean_nat_add(v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 4, v_impl_3819_);
lean_ctor_set(v___x_3848_, 3, v_r_3843_);
lean_ctor_set(v___x_3848_, 2, v_v_3327_);
lean_ctor_set(v___x_3848_, 1, v_k_3326_);
lean_ctor_set(v___x_3848_, 0, v___x_3856_);
v___x_3858_ = v___x_3848_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3856_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v_r_3843_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_impl_3819_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v___x_3858_);
lean_ctor_set(v___x_3836_, 3, v___y_3853_);
lean_ctor_set(v___x_3836_, 2, v_v_3841_);
lean_ctor_set(v___x_3836_, 1, v_k_3840_);
lean_ctor_set(v___x_3836_, 0, v___x_3851_);
v___x_3860_ = v___x_3836_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_k_3840_);
lean_ctor_set(v_reuseFailAlloc_3861_, 2, v_v_3841_);
lean_ctor_set(v_reuseFailAlloc_3861_, 3, v___y_3853_);
lean_ctor_set(v_reuseFailAlloc_3861_, 4, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
v___jp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3866_ = lean_nat_add(v___x_3863_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec(v___x_3863_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_l_3842_);
lean_ctor_set(v___x_3331_, 3, v_l_3825_);
lean_ctor_set(v___x_3331_, 2, v_v_3824_);
lean_ctor_set(v___x_3331_, 1, v_k_3823_);
lean_ctor_set(v___x_3331_, 0, v___x_3866_);
v___x_3868_ = v___x_3331_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3823_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3824_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_l_3825_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_l_3842_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_nat_add(v___x_3820_, v_size_3821_);
lean_dec(v_size_3821_);
if (lean_obj_tag(v_r_3843_) == 0)
{
lean_object* v_size_3870_; 
v_size_3870_ = lean_ctor_get(v_r_3843_, 0);
lean_inc(v_size_3870_);
v___y_3853_ = v___x_3868_;
v___y_3854_ = v___x_3869_;
v___y_3855_ = v_size_3870_;
goto v___jp_3852_;
}
else
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v___y_3853_ = v___x_3868_;
v___y_3854_ = v___x_3869_;
v___y_3855_ = v___x_3871_;
goto v___jp_3852_;
}
}
}
}
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3886_; 
lean_del_object(v___x_3331_);
v___x_3881_ = lean_nat_add(v___x_3820_, v_size_3822_);
lean_dec(v_size_3822_);
v___x_3882_ = lean_nat_add(v___x_3881_, v_size_3821_);
lean_dec(v___x_3881_);
v___x_3883_ = lean_nat_add(v___x_3820_, v_size_3821_);
lean_dec(v_size_3821_);
v___x_3884_ = lean_nat_add(v___x_3883_, v_size_3839_);
lean_dec(v___x_3883_);
lean_inc_ref(v_impl_3819_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 4, v_impl_3819_);
lean_ctor_set(v___x_3836_, 3, v_r_3826_);
lean_ctor_set(v___x_3836_, 2, v_v_3327_);
lean_ctor_set(v___x_3836_, 1, v_k_3326_);
lean_ctor_set(v___x_3836_, 0, v___x_3884_);
v___x_3886_ = v___x_3836_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3899_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3899_, 3, v_r_3826_);
lean_ctor_set(v_reuseFailAlloc_3899_, 4, v_impl_3819_);
v___x_3886_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
v_isSharedCheck_3893_ = !lean_is_exclusive(v_impl_3819_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; 
v_unused_3894_ = lean_ctor_get(v_impl_3819_, 4);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3819_, 3);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3819_, 2);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3819_, 1);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3819_, 0);
lean_dec(v_unused_3898_);
v___x_3888_ = v_impl_3819_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_dec(v_impl_3819_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 4, v___x_3886_);
lean_ctor_set(v___x_3888_, 3, v_l_3825_);
lean_ctor_set(v___x_3888_, 2, v_v_3824_);
lean_ctor_set(v___x_3888_, 1, v_k_3823_);
lean_ctor_set(v___x_3888_, 0, v___x_3882_);
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_k_3823_);
lean_ctor_set(v_reuseFailAlloc_3892_, 2, v_v_3824_);
lean_ctor_set(v_reuseFailAlloc_3892_, 3, v_l_3825_);
lean_ctor_set(v_reuseFailAlloc_3892_, 4, v___x_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v_size_3906_ = lean_ctor_get(v_impl_3819_, 0);
lean_inc(v_size_3906_);
v___x_3907_ = lean_nat_add(v___x_3820_, v_size_3906_);
lean_dec(v_size_3906_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_impl_3819_);
lean_ctor_set(v___x_3331_, 0, v___x_3907_);
v___x_3909_ = v___x_3331_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v_impl_3819_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
else
{
if (lean_obj_tag(v_l_3328_) == 0)
{
lean_object* v_l_3911_; 
v_l_3911_ = lean_ctor_get(v_l_3328_, 3);
if (lean_obj_tag(v_l_3911_) == 0)
{
lean_object* v_r_3912_; 
lean_inc_ref(v_l_3911_);
v_r_3912_ = lean_ctor_get(v_l_3328_, 4);
lean_inc(v_r_3912_);
if (lean_obj_tag(v_r_3912_) == 0)
{
lean_object* v_size_3913_; lean_object* v_k_3914_; lean_object* v_v_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3928_; 
v_size_3913_ = lean_ctor_get(v_l_3328_, 0);
v_k_3914_ = lean_ctor_get(v_l_3328_, 1);
v_v_3915_ = lean_ctor_get(v_l_3328_, 2);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; lean_object* v_unused_3930_; 
v_unused_3929_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3930_);
v___x_3917_ = v_l_3328_;
v_isShared_3918_ = v_isSharedCheck_3928_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_v_3915_);
lean_inc(v_k_3914_);
lean_inc(v_size_3913_);
lean_dec(v_l_3328_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3928_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v_size_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3923_; 
v_size_3919_ = lean_ctor_get(v_r_3912_, 0);
v___x_3920_ = lean_nat_add(v___x_3820_, v_size_3913_);
lean_dec(v_size_3913_);
v___x_3921_ = lean_nat_add(v___x_3820_, v_size_3919_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 4, v_impl_3819_);
lean_ctor_set(v___x_3917_, 3, v_r_3912_);
lean_ctor_set(v___x_3917_, 2, v_v_3327_);
lean_ctor_set(v___x_3917_, 1, v_k_3326_);
lean_ctor_set(v___x_3917_, 0, v___x_3921_);
v___x_3923_ = v___x_3917_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3927_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3927_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_r_3912_);
lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_impl_3819_);
v___x_3923_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3923_);
lean_ctor_set(v___x_3331_, 3, v_l_3911_);
lean_ctor_set(v___x_3331_, 2, v_v_3915_);
lean_ctor_set(v___x_3331_, 1, v_k_3914_);
lean_ctor_set(v___x_3331_, 0, v___x_3920_);
v___x_3925_ = v___x_3331_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_k_3914_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_v_3915_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_l_3911_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_k_3931_; lean_object* v_v_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3943_; 
v_k_3931_ = lean_ctor_get(v_l_3328_, 1);
v_v_3932_ = lean_ctor_get(v_l_3328_, 2);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; lean_object* v_unused_3945_; lean_object* v_unused_3946_; 
v_unused_3944_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3945_);
v_unused_3946_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3946_);
v___x_3934_ = v_l_3328_;
v_isShared_3935_ = v_isSharedCheck_3943_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_v_3932_);
lean_inc(v_k_3931_);
lean_dec(v_l_3328_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3943_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; lean_object* v___x_3938_; 
v___x_3936_ = lean_unsigned_to_nat(3u);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 3, v_r_3912_);
lean_ctor_set(v___x_3934_, 2, v_v_3327_);
lean_ctor_set(v___x_3934_, 1, v_k_3326_);
lean_ctor_set(v___x_3934_, 0, v___x_3820_);
v___x_3938_ = v___x_3934_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3942_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3942_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3942_, 3, v_r_3912_);
lean_ctor_set(v_reuseFailAlloc_3942_, 4, v_r_3912_);
v___x_3938_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3938_);
lean_ctor_set(v___x_3331_, 3, v_l_3911_);
lean_ctor_set(v___x_3331_, 2, v_v_3932_);
lean_ctor_set(v___x_3331_, 1, v_k_3931_);
lean_ctor_set(v___x_3331_, 0, v___x_3936_);
v___x_3940_ = v___x_3331_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3931_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3932_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v_l_3911_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
else
{
lean_object* v_r_3947_; 
v_r_3947_ = lean_ctor_get(v_l_3328_, 4);
lean_inc(v_r_3947_);
if (lean_obj_tag(v_r_3947_) == 0)
{
lean_object* v_k_3948_; lean_object* v_v_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3972_; 
lean_inc(v_l_3911_);
v_k_3948_ = lean_ctor_get(v_l_3328_, 1);
v_v_3949_ = lean_ctor_get(v_l_3328_, 2);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3972_ == 0)
{
lean_object* v_unused_3973_; lean_object* v_unused_3974_; lean_object* v_unused_3975_; 
v_unused_3973_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3973_);
v_unused_3974_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3974_);
v_unused_3975_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3975_);
v___x_3951_ = v_l_3328_;
v_isShared_3952_ = v_isSharedCheck_3972_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_v_3949_);
lean_inc(v_k_3948_);
lean_dec(v_l_3328_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3972_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v_k_3953_; lean_object* v_v_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3968_; 
v_k_3953_ = lean_ctor_get(v_r_3947_, 1);
v_v_3954_ = lean_ctor_get(v_r_3947_, 2);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_r_3947_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; lean_object* v_unused_3970_; lean_object* v_unused_3971_; 
v_unused_3969_ = lean_ctor_get(v_r_3947_, 4);
lean_dec(v_unused_3969_);
v_unused_3970_ = lean_ctor_get(v_r_3947_, 3);
lean_dec(v_unused_3970_);
v_unused_3971_ = lean_ctor_get(v_r_3947_, 0);
lean_dec(v_unused_3971_);
v___x_3956_ = v_r_3947_;
v_isShared_3957_ = v_isSharedCheck_3968_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_v_3954_);
lean_inc(v_k_3953_);
lean_dec(v_r_3947_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3968_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3958_ = lean_unsigned_to_nat(3u);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 4, v_l_3911_);
lean_ctor_set(v___x_3956_, 3, v_l_3911_);
lean_ctor_set(v___x_3956_, 2, v_v_3949_);
lean_ctor_set(v___x_3956_, 1, v_k_3948_);
lean_ctor_set(v___x_3956_, 0, v___x_3820_);
v___x_3960_ = v___x_3956_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_k_3948_);
lean_ctor_set(v_reuseFailAlloc_3967_, 2, v_v_3949_);
lean_ctor_set(v_reuseFailAlloc_3967_, 3, v_l_3911_);
lean_ctor_set(v_reuseFailAlloc_3967_, 4, v_l_3911_);
v___x_3960_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3962_; 
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 4, v_l_3911_);
lean_ctor_set(v___x_3951_, 2, v_v_3327_);
lean_ctor_set(v___x_3951_, 1, v_k_3326_);
lean_ctor_set(v___x_3951_, 0, v___x_3820_);
v___x_3962_ = v___x_3951_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3966_, 3, v_l_3911_);
lean_ctor_set(v_reuseFailAlloc_3966_, 4, v_l_3911_);
v___x_3962_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3964_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3962_);
lean_ctor_set(v___x_3331_, 3, v___x_3960_);
lean_ctor_set(v___x_3331_, 2, v_v_3954_);
lean_ctor_set(v___x_3331_, 1, v_k_3953_);
lean_ctor_set(v___x_3331_, 0, v___x_3958_);
v___x_3964_ = v___x_3331_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_k_3953_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_v_3954_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v___x_3962_);
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
}
}
else
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = lean_unsigned_to_nat(2u);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_r_3947_);
lean_ctor_set(v___x_3331_, 0, v___x_3976_);
v___x_3978_ = v___x_3331_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_r_3947_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v___x_3981_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_l_3328_);
lean_ctor_set(v___x_3331_, 0, v___x_3820_);
v___x_3981_ = v___x_3331_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_k_3326_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_v_3327_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_l_3328_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
}
}
else
{
return v_t_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3985_, lean_object* v_t_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3985_, v_t_3986_);
lean_dec(v_k_3985_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3988_, lean_object* v_x_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3988_, v_x_3989_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3991_, lean_object* v_x_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3991_, v_x_3992_);
lean_dec(v_declName_3991_);
return v_res_3993_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3996_ = l_Lean_stringToMessageData(v___x_3995_);
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v_env_4006_; lean_object* v___f_4007_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___x_4051_; 
v___x_4005_ = lean_st_ref_get(v___y_4003_);
v_env_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_ref(v_env_4006_);
lean_dec(v___x_4005_);
lean_inc(v_declName_3997_);
v___f_4007_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4007_, 0, v_declName_3997_);
v___x_4051_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4006_, v_declName_3997_);
lean_dec_ref(v_env_4006_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_dec(v_declName_3997_);
v___y_4009_ = v___y_4001_;
v___y_4010_ = v___y_4003_;
goto v___jp_4008_;
}
else
{
uint8_t v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
lean_dec_ref_known(v___x_4051_, 1);
lean_dec_ref(v___f_4007_);
v___x_4052_ = 0;
v___x_4053_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4054_ = l_Lean_MessageData_ofConstName(v_declName_3997_, v___x_4052_);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4053_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4057_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v___x_4058_;
}
v___jp_4008_:
{
lean_object* v___x_4011_; lean_object* v_env_4012_; lean_object* v_nextMacroScope_4013_; lean_object* v_ngen_4014_; lean_object* v_auxDeclNGen_4015_; lean_object* v_traceState_4016_; lean_object* v_messages_4017_; lean_object* v_infoState_4018_; lean_object* v_snapshotTasks_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4049_; 
v___x_4011_ = lean_st_ref_take(v___y_4010_);
v_env_4012_ = lean_ctor_get(v___x_4011_, 0);
v_nextMacroScope_4013_ = lean_ctor_get(v___x_4011_, 1);
v_ngen_4014_ = lean_ctor_get(v___x_4011_, 2);
v_auxDeclNGen_4015_ = lean_ctor_get(v___x_4011_, 3);
v_traceState_4016_ = lean_ctor_get(v___x_4011_, 4);
v_messages_4017_ = lean_ctor_get(v___x_4011_, 6);
v_infoState_4018_ = lean_ctor_get(v___x_4011_, 7);
v_snapshotTasks_4019_ = lean_ctor_get(v___x_4011_, 8);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v___x_4011_, 5);
lean_dec(v_unused_4050_);
v___x_4021_ = v___x_4011_;
v_isShared_4022_ = v_isSharedCheck_4049_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_snapshotTasks_4019_);
lean_inc(v_infoState_4018_);
lean_inc(v_messages_4017_);
lean_inc(v_traceState_4016_);
lean_inc(v_auxDeclNGen_4015_);
lean_inc(v_ngen_4014_);
lean_inc(v_nextMacroScope_4013_);
lean_inc(v_env_4012_);
lean_dec(v___x_4011_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4049_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4029_; 
v___x_4023_ = l_Lean_docStringExt;
v___x_4024_ = lean_box(2);
v___x_4025_ = lean_box(0);
v___x_4026_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4023_, v_env_4012_, v___f_4007_, v___x_4024_, v___x_4025_);
v___x_4027_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 5, v___x_4027_);
lean_ctor_set(v___x_4021_, 0, v___x_4026_);
v___x_4029_ = v___x_4021_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4026_);
lean_ctor_set(v_reuseFailAlloc_4048_, 1, v_nextMacroScope_4013_);
lean_ctor_set(v_reuseFailAlloc_4048_, 2, v_ngen_4014_);
lean_ctor_set(v_reuseFailAlloc_4048_, 3, v_auxDeclNGen_4015_);
lean_ctor_set(v_reuseFailAlloc_4048_, 4, v_traceState_4016_);
lean_ctor_set(v_reuseFailAlloc_4048_, 5, v___x_4027_);
lean_ctor_set(v_reuseFailAlloc_4048_, 6, v_messages_4017_);
lean_ctor_set(v_reuseFailAlloc_4048_, 7, v_infoState_4018_);
lean_ctor_set(v_reuseFailAlloc_4048_, 8, v_snapshotTasks_4019_);
v___x_4029_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v_mctx_4032_; lean_object* v_zetaDeltaFVarIds_4033_; lean_object* v_postponed_4034_; lean_object* v_diag_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4046_; 
v___x_4030_ = lean_st_ref_put(v___y_4010_, v___x_4029_);
v___x_4031_ = lean_st_ref_take(v___y_4009_);
v_mctx_4032_ = lean_ctor_get(v___x_4031_, 0);
v_zetaDeltaFVarIds_4033_ = lean_ctor_get(v___x_4031_, 2);
v_postponed_4034_ = lean_ctor_get(v___x_4031_, 3);
v_diag_4035_ = lean_ctor_get(v___x_4031_, 4);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4046_ == 0)
{
lean_object* v_unused_4047_; 
v_unused_4047_ = lean_ctor_get(v___x_4031_, 1);
lean_dec(v_unused_4047_);
v___x_4037_ = v___x_4031_;
v_isShared_4038_ = v_isSharedCheck_4046_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_diag_4035_);
lean_inc(v_postponed_4034_);
lean_inc(v_zetaDeltaFVarIds_4033_);
lean_inc(v_mctx_4032_);
lean_dec(v___x_4031_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4046_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4039_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 1, v___x_4039_);
v___x_4041_ = v___x_4037_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_mctx_4032_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4045_, 2, v_zetaDeltaFVarIds_4033_);
lean_ctor_set(v_reuseFailAlloc_4045_, 3, v_postponed_4034_);
lean_ctor_set(v_reuseFailAlloc_4045_, 4, v_diag_4035_);
v___x_4041_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4042_ = lean_st_ref_put(v___y_4009_, v___x_4041_);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4067_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4076_ = l_Lean_stringToMessageData(v___x_4075_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4079_ = l_Lean_stringToMessageData(v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_){
_start:
{
lean_object* v___x_4088_; lean_object* v_env_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; 
v___x_4088_ = lean_st_ref_get(v_a_4086_);
v_env_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc_ref(v_env_4089_);
lean_dec(v___x_4088_);
v___x_4090_ = 1;
lean_inc(v_declName_4080_);
v___x_4091_ = l_Lean_findInternalDocString_x3f(v_env_4089_, v_declName_4080_, v___x_4090_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
if (lean_obj_tag(v_a_4092_) == 1)
{
lean_object* v_val_4093_; 
v_val_4093_ = lean_ctor_get(v_a_4092_, 0);
lean_inc(v_val_4093_);
lean_dec_ref_known(v_a_4092_, 1);
if (lean_obj_tag(v_val_4093_) == 0)
{
lean_object* v_val_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4116_; 
v_val_4094_ = lean_ctor_get(v_val_4093_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v_val_4093_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4096_ = v_val_4093_;
v_isShared_4097_ = v_isSharedCheck_4116_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_val_4094_);
lean_dec(v_val_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4116_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_removeBuiltinDocString(v_declName_4080_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v___x_4099_; 
lean_dec_ref_known(v___x_4098_, 1);
lean_del_object(v___x_4096_);
lean_inc(v_declName_4080_);
v___x_4099_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v___x_4100_; 
lean_dec_ref_known(v___x_4099_, 1);
v___x_4100_ = l_Lean_addVersoDocStringFromString(v_declName_4080_, v_val_4094_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4100_;
}
else
{
lean_dec(v_val_4094_);
lean_dec(v_declName_4080_);
return v___x_4099_;
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_val_4094_);
lean_dec(v_declName_4080_);
v_a_4101_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4103_ = v___x_4098_;
v_isShared_4104_ = v_isSharedCheck_4115_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4098_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4115_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v_ref_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v_ref_4105_ = lean_ctor_get(v_a_4085_, 4);
v___x_4106_ = lean_io_error_to_string(v_a_4101_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set_tag(v___x_4096_, 3);
lean_ctor_set(v___x_4096_, 0, v___x_4106_);
v___x_4108_ = v___x_4096_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4112_; 
v___x_4109_ = l_Lean_MessageData_ofFormat(v___x_4108_);
lean_inc(v_ref_4105_);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_ref_4105_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set(v___x_4103_, 0, v___x_4110_);
v___x_4112_ = v___x_4103_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
}
}
else
{
lean_object* v___x_4117_; uint8_t v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec(v_val_4093_);
v___x_4117_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4118_ = 0;
v___x_4119_ = l_Lean_MessageData_ofConstName(v_declName_4080_, v___x_4118_);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4117_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4122_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4123_;
}
}
else
{
lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec(v_a_4092_);
v___x_4124_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4125_ = 0;
v___x_4126_ = l_Lean_MessageData_ofConstName(v_declName_4080_, v___x_4125_);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4124_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4129_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
return v___x_4130_;
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_declName_4080_);
v_a_4131_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4133_ = v___x_4091_;
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4091_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4143_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_ref_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
v_ref_4135_ = lean_ctor_get(v_a_4085_, 4);
v___x_4136_ = lean_io_error_to_string(v_a_4131_);
v___x_4137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
v___x_4138_ = l_Lean_MessageData_ofFormat(v___x_4137_);
lean_inc(v_ref_4135_);
v___x_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4139_, 0, v_ref_4135_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4139_);
v___x_4141_ = v___x_4133_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v___x_4139_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_makeDocStringVerso(v_declName_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_);
lean_dec(v_a_4150_);
lean_dec_ref(v_a_4149_);
lean_dec(v_a_4148_);
lean_dec_ref(v_a_4147_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4153_, lean_object* v_k_4154_, lean_object* v_t_4155_, lean_object* v_h_4156_){
_start:
{
lean_object* v___x_4157_; 
v___x_4157_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4154_, v_t_4155_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4158_, lean_object* v_k_4159_, lean_object* v_t_4160_, lean_object* v_h_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4158_, v_k_4159_, v_t_4160_, v_h_4161_);
lean_dec(v_k_4159_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4163_, lean_object* v_binders_4164_, lean_object* v_docComment_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
uint8_t v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = l_Lean_isVersoDocComment(v_docComment_4165_);
v___x_4174_ = l_Lean_addDocStringOf(v___x_4173_, v_declName_4163_, v_binders_4164_, v_docComment_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4175_, lean_object* v_binders_4176_, lean_object* v_docComment_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_addDocString(v_declName_4175_, v_binders_4176_, v_docComment_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4186_, lean_object* v_binders_4187_, lean_object* v_docString_x3f_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4188_) == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_dec(v_binders_4187_);
lean_dec(v_declName_4186_);
v___x_4196_ = lean_box(0);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
else
{
lean_object* v_val_4198_; lean_object* v___x_4199_; 
v_val_4198_ = lean_ctor_get(v_docString_x3f_4188_, 0);
lean_inc(v_val_4198_);
lean_dec_ref_known(v_docString_x3f_4188_, 1);
v___x_4199_ = l_Lean_addDocString(v_declName_4186_, v_binders_4187_, v_val_4198_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
return v___x_4199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4200_, lean_object* v_binders_4201_, lean_object* v_docString_x3f_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_addDocString_x27(v_declName_4200_, v_binders_4201_, v_docString_x3f_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_, v_a_4208_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
lean_dec(v_a_4206_);
lean_dec_ref(v_a_4205_);
lean_dec(v_a_4204_);
lean_dec_ref(v_a_4203_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___x_4215_; lean_object* v_nextMacroScope_4216_; lean_object* v_ngen_4217_; lean_object* v_auxDeclNGen_4218_; lean_object* v_traceState_4219_; lean_object* v_messages_4220_; lean_object* v_infoState_4221_; lean_object* v_snapshotTasks_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4248_; 
v___x_4215_ = lean_st_ref_take(v___y_4213_);
v_nextMacroScope_4216_ = lean_ctor_get(v___x_4215_, 1);
v_ngen_4217_ = lean_ctor_get(v___x_4215_, 2);
v_auxDeclNGen_4218_ = lean_ctor_get(v___x_4215_, 3);
v_traceState_4219_ = lean_ctor_get(v___x_4215_, 4);
v_messages_4220_ = lean_ctor_get(v___x_4215_, 6);
v_infoState_4221_ = lean_ctor_get(v___x_4215_, 7);
v_snapshotTasks_4222_ = lean_ctor_get(v___x_4215_, 8);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4248_ == 0)
{
lean_object* v_unused_4249_; lean_object* v_unused_4250_; 
v_unused_4249_ = lean_ctor_get(v___x_4215_, 5);
lean_dec(v_unused_4249_);
v_unused_4250_ = lean_ctor_get(v___x_4215_, 0);
lean_dec(v_unused_4250_);
v___x_4224_ = v___x_4215_;
v_isShared_4225_ = v_isSharedCheck_4248_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_snapshotTasks_4222_);
lean_inc(v_infoState_4221_);
lean_inc(v_messages_4220_);
lean_inc(v_traceState_4219_);
lean_inc(v_auxDeclNGen_4218_);
lean_inc(v_ngen_4217_);
lean_inc(v_nextMacroScope_4216_);
lean_dec(v___x_4215_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4248_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4226_; lean_object* v___x_4228_; 
v___x_4226_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 5, v___x_4226_);
lean_ctor_set(v___x_4224_, 0, v_env_4211_);
v___x_4228_ = v___x_4224_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_env_4211_);
lean_ctor_set(v_reuseFailAlloc_4247_, 1, v_nextMacroScope_4216_);
lean_ctor_set(v_reuseFailAlloc_4247_, 2, v_ngen_4217_);
lean_ctor_set(v_reuseFailAlloc_4247_, 3, v_auxDeclNGen_4218_);
lean_ctor_set(v_reuseFailAlloc_4247_, 4, v_traceState_4219_);
lean_ctor_set(v_reuseFailAlloc_4247_, 5, v___x_4226_);
lean_ctor_set(v_reuseFailAlloc_4247_, 6, v_messages_4220_);
lean_ctor_set(v_reuseFailAlloc_4247_, 7, v_infoState_4221_);
lean_ctor_set(v_reuseFailAlloc_4247_, 8, v_snapshotTasks_4222_);
v___x_4228_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v_mctx_4231_; lean_object* v_zetaDeltaFVarIds_4232_; lean_object* v_postponed_4233_; lean_object* v_diag_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4245_; 
v___x_4229_ = lean_st_ref_put(v___y_4213_, v___x_4228_);
v___x_4230_ = lean_st_ref_take(v___y_4212_);
v_mctx_4231_ = lean_ctor_get(v___x_4230_, 0);
v_zetaDeltaFVarIds_4232_ = lean_ctor_get(v___x_4230_, 2);
v_postponed_4233_ = lean_ctor_get(v___x_4230_, 3);
v_diag_4234_ = lean_ctor_get(v___x_4230_, 4);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v___x_4230_, 1);
lean_dec(v_unused_4246_);
v___x_4236_ = v___x_4230_;
v_isShared_4237_ = v_isSharedCheck_4245_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_diag_4234_);
lean_inc(v_postponed_4233_);
lean_inc(v_zetaDeltaFVarIds_4232_);
lean_inc(v_mctx_4231_);
lean_dec(v___x_4230_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4245_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4238_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 1, v___x_4238_);
v___x_4240_ = v___x_4236_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_mctx_4231_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4238_);
lean_ctor_set(v_reuseFailAlloc_4244_, 2, v_zetaDeltaFVarIds_4232_);
lean_ctor_set(v_reuseFailAlloc_4244_, 3, v_postponed_4233_);
lean_ctor_set(v_reuseFailAlloc_4244_, 4, v_diag_4234_);
v___x_4240_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4241_ = lean_st_ref_put(v___y_4212_, v___x_4240_);
v___x_4242_ = lean_box(0);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
return v___x_4243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec(v___y_4252_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4256_, lean_object* v_as_4257_, size_t v_i_4258_, size_t v_stop_4259_, lean_object* v_b_4260_){
_start:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_usize_dec_eq(v_i_4258_, v_stop_4259_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v_index_4263_; lean_object* v_sourceString_4264_; lean_object* v_imports_4265_; lean_object* v_currNamespace_4266_; lean_object* v_openDecls_4267_; lean_object* v_options_4268_; lean_object* v_check_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4285_; 
v___x_4262_ = lean_array_uget(v_as_4257_, v_i_4258_);
v_index_4263_ = lean_ctor_get(v___x_4262_, 1);
v_sourceString_4264_ = lean_ctor_get(v___x_4262_, 2);
v_imports_4265_ = lean_ctor_get(v___x_4262_, 3);
v_currNamespace_4266_ = lean_ctor_get(v___x_4262_, 4);
v_openDecls_4267_ = lean_ctor_get(v___x_4262_, 5);
v_options_4268_ = lean_ctor_get(v___x_4262_, 6);
v_check_4269_ = lean_ctor_get(v___x_4262_, 7);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4285_ == 0)
{
lean_object* v_unused_4286_; 
v_unused_4286_ = lean_ctor_get(v___x_4262_, 0);
lean_dec(v_unused_4286_);
v___x_4271_ = v___x_4262_;
v_isShared_4272_ = v_isSharedCheck_4285_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_check_4269_);
lean_inc(v_options_4268_);
lean_inc(v_openDecls_4267_);
lean_inc(v_currNamespace_4266_);
lean_inc(v_imports_4265_);
lean_inc(v_sourceString_4264_);
lean_inc(v_index_4263_);
lean_dec(v___x_4262_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4285_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4273_; lean_object* v_toEnvExtension_4274_; lean_object* v_asyncMode_4275_; lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4273_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4274_ = lean_ctor_get(v___x_4273_, 0);
v_asyncMode_4275_ = lean_ctor_get(v_toEnvExtension_4274_, 2);
lean_inc(v_n_4256_);
v___x_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_n_4256_);
if (v_isShared_4272_ == 0)
{
lean_ctor_set(v___x_4271_, 0, v___x_4276_);
v___x_4278_ = v___x_4271_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_index_4263_);
lean_ctor_set(v_reuseFailAlloc_4284_, 2, v_sourceString_4264_);
lean_ctor_set(v_reuseFailAlloc_4284_, 3, v_imports_4265_);
lean_ctor_set(v_reuseFailAlloc_4284_, 4, v_currNamespace_4266_);
lean_ctor_set(v_reuseFailAlloc_4284_, 5, v_openDecls_4267_);
lean_ctor_set(v_reuseFailAlloc_4284_, 6, v_options_4268_);
lean_ctor_set(v_reuseFailAlloc_4284_, 7, v_check_4269_);
v___x_4278_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; size_t v___x_4281_; size_t v___x_4282_; 
v___x_4279_ = lean_box(0);
v___x_4280_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4273_, v_b_4260_, v___x_4278_, v_asyncMode_4275_, v___x_4279_);
v___x_4281_ = ((size_t)1ULL);
v___x_4282_ = lean_usize_add(v_i_4258_, v___x_4281_);
v_i_4258_ = v___x_4282_;
v_b_4260_ = v___x_4280_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4256_);
return v_b_4260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4287_, lean_object* v_as_4288_, lean_object* v_i_4289_, lean_object* v_stop_4290_, lean_object* v_b_4291_){
_start:
{
size_t v_i_boxed_4292_; size_t v_stop_boxed_4293_; lean_object* v_res_4294_; 
v_i_boxed_4292_ = lean_unbox_usize(v_i_4289_);
lean_dec(v_i_4289_);
v_stop_boxed_4293_ = lean_unbox_usize(v_stop_4290_);
lean_dec(v_stop_4290_);
v_res_4294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4287_, v_as_4288_, v_i_boxed_4292_, v_stop_boxed_4293_, v_b_4291_);
lean_dec_ref(v_as_4288_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4295_, lean_object* v_deferred_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v___x_4304_; lean_object* v_env_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4304_ = lean_st_ref_get(v___y_4302_);
v_env_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc_ref(v_env_4305_);
lean_dec(v___x_4304_);
v___x_4306_ = l_Lean_getMainModuleDoc(v_env_4305_);
v___x_4307_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4306_);
lean_dec_ref(v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_dec_ref(v_docs_4295_);
v___x_4308_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4309_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4308_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
return v___x_4309_;
}
else
{
lean_object* v___x_4310_; lean_object* v_env_4311_; lean_object* v___x_4312_; lean_object* v_size_4313_; lean_object* v___x_4314_; lean_object* v_env_4315_; lean_object* v___x_4316_; 
v___x_4310_ = lean_st_ref_get(v___y_4302_);
v_env_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc_ref(v_env_4311_);
lean_dec(v___x_4310_);
v___x_4312_ = l_Lean_getMainVersoModuleDocs(v_env_4311_);
v_size_4313_ = lean_ctor_get(v___x_4312_, 2);
lean_inc(v_size_4313_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = lean_st_ref_get(v___y_4302_);
v_env_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc_ref(v_env_4315_);
lean_dec(v___x_4314_);
v___x_4316_ = l_Lean_addVersoModuleDocSnippet(v_env_4315_, v_docs_4295_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
lean_dec(v_size_4313_);
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4319_ = l_Lean_stringToMessageData(v_a_4317_);
v___x_4320_ = l_Lean_indentD(v___x_4319_);
v___x_4321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4318_);
lean_ctor_set(v___x_4321_, 1, v___x_4320_);
v___x_4322_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4321_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
return v___x_4322_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v_a_4323_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4324_ = lean_unsigned_to_nat(0u);
v___x_4325_ = lean_array_get_size(v_deferred_4296_);
v___x_4326_ = lean_nat_dec_lt(v___x_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
lean_dec(v_size_4313_);
v___x_4327_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4323_, v___y_4300_, v___y_4302_);
return v___x_4327_;
}
else
{
size_t v___x_4328_; size_t v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4328_ = ((size_t)0ULL);
v___x_4329_ = lean_usize_of_nat(v___x_4325_);
v___x_4330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4313_, v_deferred_4296_, v___x_4328_, v___x_4329_, v_a_4323_);
v___x_4331_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4330_, v___y_4300_, v___y_4302_);
return v___x_4331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4332_, lean_object* v_deferred_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4332_, v_deferred_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec_ref(v_deferred_4333_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4342_, lean_object* v_docComment_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_versoModDocString(v_range_4342_, v_docComment_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v_fst_4353_; lean_object* v_snd_4354_; lean_object* v___x_4355_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v_fst_4353_ = lean_ctor_get(v_a_4352_, 0);
lean_inc(v_fst_4353_);
v_snd_4354_ = lean_ctor_get(v_a_4352_, 1);
lean_inc(v_snd_4354_);
lean_dec(v_a_4352_);
v___x_4355_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4353_, v_snd_4354_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
lean_dec(v_snd_4354_);
return v___x_4355_;
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4351_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4351_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4364_, lean_object* v_docComment_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_addVersoModDocString(v_range_4364_, v_docComment_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
lean_dec(v_docComment_4365_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4374_, v___y_4378_, v___y_4380_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
return v_res_4391_;
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
