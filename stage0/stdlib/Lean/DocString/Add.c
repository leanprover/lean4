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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t v___x_1476__boxed_173_; lean_object* v_res_174_; 
v___x_1476__boxed_173_ = lean_unbox(v___x_168_);
v_res_174_ = l_Lean_parseVersoDocString___redArg___lam__3(v_text_165_, v_fst_166_, v_snd_167_, v___x_1476__boxed_173_, v_logMessage_169_, v_toBind_170_, v___f_171_, v_____do__lift_172_);
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
uint8_t v___x_1510__boxed_199_; lean_object* v_res_200_; 
v___x_1510__boxed_199_ = lean_unbox(v___x_191_);
v_res_200_ = l_Lean_parseVersoDocString___redArg___lam__4(v_text_190_, v___x_1510__boxed_199_, v_logMessage_192_, v_toBind_193_, v___f_194_, v_getFileName_195_, v_a_196_, v_x_197_, v___y_198_);
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
uint8_t v___x_1540__boxed_234_; lean_object* v_res_235_; 
v___x_1540__boxed_234_ = lean_unbox(v___x_229_);
v_res_235_ = l_Lean_parseVersoDocString___redArg___lam__5(v_text_226_, v_pos_227_, v_source_228_, v___x_1540__boxed_234_, v_logMessage_230_, v_toBind_231_, v___f_232_, v_____do__lift_233_);
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
lean_dec_ref_known(v_pre_480_, 2);
lean_dec(v_pre_481_);
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
lean_dec(v_pre_480_);
lean_dec_ref_known(v_pre_479_, 2);
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
lean_dec_ref_known(v_pre_478_, 2);
lean_dec(v_pre_479_);
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
lean_dec(v_pre_478_);
lean_dec_ref_known(v_kind_477_, 2);
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
uint8_t v___x_9777__boxed_858_; lean_object* v_res_859_; 
v___x_9777__boxed_858_ = lean_unbox(v___x_850_);
v_res_859_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_846_, v_declName_847_, v_binders_848_, v___x_849_, v___x_9777__boxed_858_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
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
uint8_t v_suppressElabErrors_boxed_953_; uint8_t v___y_9876__boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_suppressElabErrors_boxed_953_ = lean_unbox(v_suppressElabErrors_950_);
v___y_9876__boxed_954_ = lean_unbox(v___y_951_);
v_res_955_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_953_, v___y_9876__boxed_954_, v_x_952_);
lean_dec(v_x_952_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_957_, lean_object* v_msgData_958_, uint8_t v_severity_959_, uint8_t v_isSilent_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___y_967_; lean_object* v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v_currNamespace_974_; lean_object* v_openDecls_975_; lean_object* v___y_976_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; uint8_t v___y_1008_; uint8_t v___y_1009_; uint8_t v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; uint8_t v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; uint8_t v___y_1048_; uint8_t v___y_1049_; uint8_t v___y_1050_; uint8_t v___x_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1064_; uint8_t v___y_1065_; uint8_t v___y_1067_; uint8_t v___x_1085_; 
v___x_1055_ = 2;
v___x_1085_ = l_Lean_instBEqMessageSeverity_beq(v_severity_959_, v___x_1055_);
if (v___x_1085_ == 0)
{
v___y_1067_ = v___x_1085_;
goto v___jp_1066_;
}
else
{
uint8_t v___x_1086_; 
lean_inc_ref(v_msgData_958_);
v___x_1086_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_958_);
v___y_1067_ = v___x_1086_;
goto v___jp_1066_;
}
v___jp_966_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_env_981_; lean_object* v_nextMacroScope_982_; lean_object* v_ngen_983_; lean_object* v_auxDeclNGen_984_; lean_object* v_traceState_985_; lean_object* v_cache_986_; lean_object* v_messages_987_; lean_object* v_infoState_988_; lean_object* v_snapshotTasks_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1000_; 
lean_inc(v_openDecls_975_);
lean_inc(v_currNamespace_974_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v_currNamespace_974_);
lean_ctor_set(v___x_977_, 1, v_openDecls_975_);
v___x_978_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___y_972_);
lean_inc_ref(v___y_968_);
lean_inc_ref(v___y_967_);
v___x_979_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_979_, 0, v___y_967_);
lean_ctor_set(v___x_979_, 1, v___y_971_);
lean_ctor_set(v___x_979_, 2, v___y_970_);
lean_ctor_set(v___x_979_, 3, v___y_968_);
lean_ctor_set(v___x_979_, 4, v___x_978_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*5, v___y_973_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*5 + 1, v___y_969_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*5 + 2, v_isSilent_960_);
v___x_980_ = lean_st_ref_take(v___y_976_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
v_nextMacroScope_982_ = lean_ctor_get(v___x_980_, 1);
v_ngen_983_ = lean_ctor_get(v___x_980_, 2);
v_auxDeclNGen_984_ = lean_ctor_get(v___x_980_, 3);
v_traceState_985_ = lean_ctor_get(v___x_980_, 4);
v_cache_986_ = lean_ctor_get(v___x_980_, 5);
v_messages_987_ = lean_ctor_get(v___x_980_, 6);
v_infoState_988_ = lean_ctor_get(v___x_980_, 7);
v_snapshotTasks_989_ = lean_ctor_get(v___x_980_, 8);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_991_ = v___x_980_;
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_snapshotTasks_989_);
lean_inc(v_infoState_988_);
lean_inc(v_messages_987_);
lean_inc(v_cache_986_);
lean_inc(v_traceState_985_);
lean_inc(v_auxDeclNGen_984_);
lean_inc(v_ngen_983_);
lean_inc(v_nextMacroScope_982_);
lean_inc(v_env_981_);
lean_dec(v___x_980_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_993_ = lean_box(0);
v___x_994_ = l_Lean_MessageLog_add(v___x_979_, v_messages_987_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 6, v___x_994_);
v___x_996_ = v___x_991_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_env_981_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_nextMacroScope_982_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_ngen_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_auxDeclNGen_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_traceState_985_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_cache_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 6, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_999_, 7, v_infoState_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 8, v_snapshotTasks_989_);
v___x_996_ = v_reuseFailAlloc_999_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_st_ref_put(v___y_976_, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v___x_993_);
return v___x_998_;
}
}
}
v___jp_1001_:
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
lean_inc_ref_n(v___y_1005_, 2);
v___x_1018_ = l_Lean_FileMap_toPosition(v___y_1005_, v___y_1007_);
lean_dec(v___y_1007_);
v___x_1019_ = l_Lean_FileMap_toPosition(v___y_1005_, v___y_1011_);
lean_dec(v___y_1011_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
v___x_1021_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
if (v___y_1009_ == 0)
{
lean_del_object(v___x_1016_);
lean_dec_ref(v___y_1003_);
v___y_967_ = v___y_1006_;
v___y_968_ = v___x_1021_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___x_1020_;
v___y_971_ = v___x_1018_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___y_1010_;
v_currNamespace_974_ = v___y_1002_;
v_openDecls_975_ = v___y_1004_;
v___y_976_ = v___y_964_;
goto v___jp_966_;
}
else
{
uint8_t v___x_1022_; 
lean_inc(v_a_1014_);
v___x_1022_ = l_Lean_MessageData_hasTag(v___y_1003_, v_a_1014_);
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
v___y_967_ = v___y_1006_;
v___y_968_ = v___x_1021_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___x_1020_;
v___y_971_ = v___x_1018_;
v___y_972_ = v_a_1014_;
v___y_973_ = v___y_1010_;
v_currNamespace_974_ = v___y_1002_;
v_openDecls_975_ = v___y_1004_;
v___y_976_ = v___y_964_;
goto v___jp_966_;
}
}
}
}
v___jp_1028_:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Syntax_getTailPos_x3f(v___y_1033_, v___y_1037_);
lean_dec(v___y_1033_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_inc(v___y_1038_);
v___y_1002_ = v___y_1029_;
v___y_1003_ = v___y_1030_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1032_;
v___y_1006_ = v___y_1034_;
v___y_1007_ = v___y_1038_;
v___y_1008_ = v___y_1035_;
v___y_1009_ = v___y_1036_;
v___y_1010_ = v___y_1037_;
v___y_1011_ = v___y_1038_;
goto v___jp_1001_;
}
else
{
lean_object* v_val_1040_; 
v_val_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_val_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v___y_1002_ = v___y_1029_;
v___y_1003_ = v___y_1030_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1032_;
v___y_1006_ = v___y_1034_;
v___y_1007_ = v___y_1038_;
v___y_1008_ = v___y_1035_;
v___y_1009_ = v___y_1036_;
v___y_1010_ = v___y_1037_;
v___y_1011_ = v_val_1040_;
goto v___jp_1001_;
}
}
v___jp_1041_:
{
lean_object* v_ref_1051_; lean_object* v___x_1052_; 
v_ref_1051_ = l_Lean_replaceRef(v_ref_957_, v___y_1047_);
v___x_1052_ = l_Lean_Syntax_getPos_x3f(v_ref_1051_, v___y_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_unsigned_to_nat(0u);
v___y_1029_ = v___y_1042_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1045_;
v___y_1033_ = v_ref_1051_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v___y_1050_;
v___y_1036_ = v___y_1048_;
v___y_1037_ = v___y_1049_;
v___y_1038_ = v___x_1053_;
goto v___jp_1028_;
}
else
{
lean_object* v_val_1054_; 
v_val_1054_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v___x_1052_, 1);
v___y_1029_ = v___y_1042_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___y_1044_;
v___y_1032_ = v___y_1045_;
v___y_1033_ = v_ref_1051_;
v___y_1034_ = v___y_1046_;
v___y_1035_ = v___y_1050_;
v___y_1036_ = v___y_1048_;
v___y_1037_ = v___y_1049_;
v___y_1038_ = v_val_1054_;
goto v___jp_1028_;
}
}
v___jp_1056_:
{
if (v___y_1065_ == 0)
{
v___y_1042_ = v___y_1059_;
v___y_1043_ = v___y_1060_;
v___y_1044_ = v___y_1061_;
v___y_1045_ = v___y_1057_;
v___y_1046_ = v___y_1058_;
v___y_1047_ = v___y_1062_;
v___y_1048_ = v___y_1063_;
v___y_1049_ = v___y_1064_;
v___y_1050_ = v_severity_959_;
goto v___jp_1041_;
}
else
{
v___y_1042_ = v___y_1059_;
v___y_1043_ = v___y_1060_;
v___y_1044_ = v___y_1061_;
v___y_1045_ = v___y_1057_;
v___y_1046_ = v___y_1058_;
v___y_1047_ = v___y_1062_;
v___y_1048_ = v___y_1063_;
v___y_1049_ = v___y_1064_;
v___y_1050_ = v___x_1055_;
goto v___jp_1041_;
}
}
v___jp_1066_:
{
if (v___y_1067_ == 0)
{
lean_object* v_toCold_1068_; lean_object* v_ref_1069_; uint8_t v_suppressElabErrors_1070_; lean_object* v_fileName_1071_; lean_object* v_fileMap_1072_; lean_object* v_options_1073_; lean_object* v_currNamespace_1074_; lean_object* v_openDecls_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; uint8_t v___x_1079_; uint8_t v___x_1080_; 
v_toCold_1068_ = lean_ctor_get(v___y_963_, 0);
v_ref_1069_ = lean_ctor_get(v___y_963_, 2);
v_suppressElabErrors_1070_ = lean_ctor_get_uint8(v___y_963_, sizeof(void*)*3 + 1);
v_fileName_1071_ = lean_ctor_get(v_toCold_1068_, 0);
v_fileMap_1072_ = lean_ctor_get(v_toCold_1068_, 1);
v_options_1073_ = lean_ctor_get(v_toCold_1068_, 2);
v_currNamespace_1074_ = lean_ctor_get(v_toCold_1068_, 4);
v_openDecls_1075_ = lean_ctor_get(v_toCold_1068_, 5);
v___x_1076_ = lean_box(v_suppressElabErrors_1070_);
v___x_1077_ = lean_box(v___y_1067_);
v___f_1078_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1078_, 0, v___x_1076_);
lean_closure_set(v___f_1078_, 1, v___x_1077_);
v___x_1079_ = 1;
v___x_1080_ = l_Lean_instBEqMessageSeverity_beq(v_severity_959_, v___x_1079_);
if (v___x_1080_ == 0)
{
v___y_1057_ = v_fileMap_1072_;
v___y_1058_ = v_fileName_1071_;
v___y_1059_ = v_currNamespace_1074_;
v___y_1060_ = v___f_1078_;
v___y_1061_ = v_openDecls_1075_;
v___y_1062_ = v_ref_1069_;
v___y_1063_ = v_suppressElabErrors_1070_;
v___y_1064_ = v___y_1067_;
v___y_1065_ = v___x_1080_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = l_Lean_warningAsError;
v___x_1082_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1073_, v___x_1081_);
v___y_1057_ = v_fileMap_1072_;
v___y_1058_ = v_fileName_1071_;
v___y_1059_ = v_currNamespace_1074_;
v___y_1060_ = v___f_1078_;
v___y_1061_ = v_openDecls_1075_;
v___y_1062_ = v_ref_1069_;
v___y_1063_ = v_suppressElabErrors_1070_;
v___y_1064_ = v___y_1067_;
v___y_1065_ = v___x_1082_;
goto v___jp_1056_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_msgData_958_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_1087_, lean_object* v_msgData_1088_, lean_object* v_severity_1089_, lean_object* v_isSilent_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_severity_boxed_1096_; uint8_t v_isSilent_boxed_1097_; lean_object* v_res_1098_; 
v_severity_boxed_1096_ = lean_unbox(v_severity_1089_);
v_isSilent_boxed_1097_ = lean_unbox(v_isSilent_1090_);
v_res_1098_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1087_, v_msgData_1088_, v_severity_boxed_1096_, v_isSilent_boxed_1097_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v_ref_1087_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_1099_, size_t v_sz_1100_, size_t v_i_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1101_, v_sz_1100_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_b_1102_);
return v___x_1111_;
}
else
{
lean_object* v_ref_1112_; lean_object* v_a_1113_; uint8_t v_severity_1114_; uint8_t v_isSilent_1115_; lean_object* v_data_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_ref_1112_ = lean_ctor_get(v___y_1107_, 2);
v_a_1113_ = lean_array_uget_borrowed(v_as_1099_, v_i_1101_);
v_severity_1114_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*5 + 1);
v_isSilent_1115_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*5 + 2);
v_data_1116_ = lean_ctor_get(v_a_1113_, 4);
v___x_1117_ = lean_box(0);
lean_inc(v_data_1116_);
v___x_1118_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1112_, v_data_1116_, v_severity_1114_, v_isSilent_1115_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1118_) == 0)
{
size_t v___x_1119_; size_t v___x_1120_; 
lean_dec_ref_known(v___x_1118_, 1);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1101_, v___x_1119_);
v_i_1101_ = v___x_1120_;
v_b_1102_ = v___x_1117_;
goto _start;
}
else
{
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_1122_, lean_object* v_sz_1123_, lean_object* v_i_1124_, lean_object* v_b_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
size_t v_sz_boxed_1133_; size_t v_i_boxed_1134_; lean_object* v_res_1135_; 
v_sz_boxed_1133_ = lean_unbox_usize(v_sz_1123_);
lean_dec(v_sz_1123_);
v_i_boxed_1134_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_1122_, v_sz_boxed_1133_, v_i_boxed_1134_, v_b_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec_ref(v_as_1122_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v_infoState_1140_; lean_object* v_env_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_ngen_1143_; lean_object* v_auxDeclNGen_1144_; lean_object* v_traceState_1145_; lean_object* v_cache_1146_; lean_object* v_messages_1147_; lean_object* v_snapshotTasks_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1168_; 
v___x_1139_ = lean_st_ref_take(v___y_1137_);
v_infoState_1140_ = lean_ctor_get(v___x_1139_, 7);
v_env_1141_ = lean_ctor_get(v___x_1139_, 0);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1139_, 1);
v_ngen_1143_ = lean_ctor_get(v___x_1139_, 2);
v_auxDeclNGen_1144_ = lean_ctor_get(v___x_1139_, 3);
v_traceState_1145_ = lean_ctor_get(v___x_1139_, 4);
v_cache_1146_ = lean_ctor_get(v___x_1139_, 5);
v_messages_1147_ = lean_ctor_get(v___x_1139_, 6);
v_snapshotTasks_1148_ = lean_ctor_get(v___x_1139_, 8);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1150_ = v___x_1139_;
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snapshotTasks_1148_);
lean_inc(v_infoState_1140_);
lean_inc(v_messages_1147_);
lean_inc(v_cache_1146_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1144_);
lean_inc(v_ngen_1143_);
lean_inc(v_nextMacroScope_1142_);
lean_inc(v_env_1141_);
lean_dec(v___x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_assignment_1152_; lean_object* v_lazyAssignment_1153_; lean_object* v_trees_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
v_assignment_1152_ = lean_ctor_get(v_infoState_1140_, 0);
v_lazyAssignment_1153_ = lean_ctor_get(v_infoState_1140_, 1);
v_trees_1154_ = lean_ctor_get(v_infoState_1140_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_infoState_1140_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1156_ = v_infoState_1140_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_trees_1154_);
lean_inc(v_lazyAssignment_1153_);
lean_inc(v_assignment_1152_);
lean_dec(v_infoState_1140_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = lean_box(0);
if (v_isShared_1157_ == 0)
{
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_assignment_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_lazyAssignment_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_trees_1154_);
v___x_1160_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3, v_flag_1136_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 7, v___x_1160_);
v___x_1162_ = v___x_1150_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_env_1141_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_nextMacroScope_1142_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_ngen_1143_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_auxDeclNGen_1144_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_traceState_1145_);
lean_ctor_set(v_reuseFailAlloc_1165_, 5, v_cache_1146_);
lean_ctor_set(v_reuseFailAlloc_1165_, 6, v_messages_1147_);
lean_ctor_set(v_reuseFailAlloc_1165_, 7, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1165_, 8, v_snapshotTasks_1148_);
v___x_1162_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_st_ref_put(v___y_1137_, v___x_1162_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1158_);
return v___x_1164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_flag_boxed_1172_; lean_object* v_res_1173_; 
v_flag_boxed_1172_ = lean_unbox(v_flag_1169_);
v_res_1173_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1172_, v___y_1170_);
lean_dec(v___y_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_infoState_1184_; uint8_t v_enabled_1185_; lean_object* v_a_1187_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_infoState_1184_ = lean_ctor_get(v___x_1183_, 7);
lean_inc_ref(v_infoState_1184_);
lean_dec(v___x_1183_);
v_enabled_1185_ = lean_ctor_get_uint8(v_infoState_1184_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1184_);
v___x_1197_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1174_, v___y_1181_);
lean_dec_ref(v___x_1197_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc_ref(v___y_1176_);
v___x_1198_ = lean_apply_7(v_x_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, lean_box(0));
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1185_, v___y_1181_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1208_);
v___x_1202_ = v___x_1200_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v___x_1200_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_a_1199_);
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1199_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v_a_1209_; 
v_a_1209_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1198_, 1);
v_a_1187_ = v_a_1209_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v___x_1188_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1185_, v___y_1181_);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1196_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 1);
lean_ctor_set(v___x_1190_, 0, v_a_1187_);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1187_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1210_, lean_object* v_x_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_flag_boxed_1219_; lean_object* v_res_1220_; 
v_flag_boxed_1219_ = lean_unbox(v_flag_1210_);
v_res_1220_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1219_, v_x_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1221_, lean_object* v_binders_1222_, lean_object* v_blocks_1223_, lean_object* v_fileMap_x3f_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1230_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_a_1235_; size_t v_sz_1253_; size_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___y_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_sz_1253_ = lean_array_size(v_blocks_1223_);
v___x_1254_ = ((size_t)0ULL);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1253_, v___x_1254_, v_blocks_1223_);
v___x_1256_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1256_, 0, v___x_1255_);
v___x_1257_ = 1;
v___x_1258_ = lean_box(v___x_1257_);
v___y_1259_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1259_, 0, v_fileMap_x3f_1224_);
lean_closure_set(v___y_1259_, 1, v_declName_1221_);
lean_closure_set(v___y_1259_, 2, v_binders_1222_);
lean_closure_set(v___y_1259_, 3, v___x_1256_);
lean_closure_set(v___y_1259_, 4, v___x_1258_);
v___x_1260_ = 0;
v___x_1261_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1260_, v___y_1259_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1230_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = l_Lean_Core_setMessageLog___redArg(v_a_1233_, v_a_1230_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1266_; lean_object* v___x_1267_; size_t v_sz_1268_; lean_object* v___x_1269_; 
lean_dec_ref_known(v___x_1265_, 1);
v___x_1266_ = l_Lean_MessageLog_toArray(v_a_1264_);
lean_dec(v_a_1264_);
v___x_1267_ = lean_box(0);
v_sz_1268_ = lean_array_size(v___x_1266_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1266_, v_sz_1268_, v___x_1254_, v___x_1267_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
lean_dec_ref(v___x_1266_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1294_; 
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1269_, 0);
lean_dec(v_unused_1295_);
v___x_1271_ = v___x_1269_;
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v___x_1269_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_fst_1273_; lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1293_; 
v_fst_1273_ = lean_ctor_get(v_a_1262_, 0);
v_snd_1274_ = lean_ctor_get(v_a_1262_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1276_ = v_a_1262_;
v_isShared_1277_ = v_isSharedCheck_1293_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_inc(v_fst_1273_);
lean_dec(v_a_1262_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1293_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1292_; 
v_fst_1278_ = lean_ctor_get(v_fst_1273_, 0);
v_snd_1279_ = lean_ctor_get(v_fst_1273_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_fst_1273_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1281_ = v_fst_1273_;
v_isShared_1282_ = v_isSharedCheck_1292_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_inc(v_fst_1278_);
lean_dec(v_fst_1273_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1292_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_snd_1279_);
v___x_1284_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1284_);
v___x_1286_ = v___x_1276_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_snd_1274_);
v___x_1286_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1288_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1286_);
v___x_1288_ = v___x_1271_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
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
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_a_1262_);
v_a_1296_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1269_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1269_);
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
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1264_);
lean_dec(v_a_1262_);
v_a_1304_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1265_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1265_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; 
lean_dec(v_a_1262_);
v_a_1312_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1263_, 1);
v_a_1235_ = v_a_1312_;
goto v___jp_1234_;
}
}
else
{
lean_object* v_a_1313_; 
v_a_1313_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1261_, 1);
v_a_1235_ = v_a_1313_;
goto v___jp_1234_;
}
v___jp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Core_setMessageLog___redArg(v_a_1233_, v_a_1230_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1236_, 0);
lean_dec(v_unused_1244_);
v___x_1238_ = v___x_1236_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set_tag(v___x_1238_, 1);
lean_ctor_set(v___x_1238_, 0, v_a_1235_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1235_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_a_1235_);
v_a_1245_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1236_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1236_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_fileMap_x3f_1224_);
lean_dec_ref(v_blocks_1223_);
lean_dec(v_binders_1222_);
lean_dec(v_declName_1221_);
v_a_1314_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1232_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1232_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1322_, lean_object* v_binders_1323_, lean_object* v_blocks_1324_, lean_object* v_fileMap_x3f_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1322_, v_binders_1323_, v_blocks_1324_, v_fileMap_x3f_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1334_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_flag_boxed_1351_; lean_object* v_res_1352_; 
v_flag_boxed_1351_ = lean_unbox(v_flag_1343_);
v_res_1352_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1351_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1353_, uint8_t v_flag_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1354_, v_x_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_flag_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_flag_boxed_1374_; lean_object* v_res_1375_; 
v_flag_boxed_1374_ = lean_unbox(v_flag_1365_);
v_res_1375_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1364_, v_flag_boxed_1374_, v_x_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1376_, lean_object* v_msgData_1377_, uint8_t v_severity_1378_, uint8_t v_isSilent_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1376_, v_msgData_1377_, v_severity_1378_, v_isSilent_1379_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1388_, lean_object* v_msgData_1389_, lean_object* v_severity_1390_, lean_object* v_isSilent_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_severity_boxed_1399_; uint8_t v_isSilent_boxed_1400_; lean_object* v_res_1401_; 
v_severity_boxed_1399_ = lean_unbox(v_severity_1390_);
v_isSilent_boxed_1400_ = lean_unbox(v_isSilent_1391_);
v_res_1401_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1388_, v_msgData_1389_, v_severity_boxed_1399_, v_isSilent_boxed_1400_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v_ref_1388_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1402_, uint8_t v_severity_1403_, uint8_t v_isSilent_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_ref_1410_; lean_object* v___x_1411_; 
v_ref_1410_ = lean_ctor_get(v___y_1407_, 2);
v___x_1411_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1410_, v_msgData_1402_, v_severity_1403_, v_isSilent_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1412_, lean_object* v_severity_1413_, lean_object* v_isSilent_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v_severity_boxed_1420_; uint8_t v_isSilent_boxed_1421_; lean_object* v_res_1422_; 
v_severity_boxed_1420_ = lean_unbox(v_severity_1413_);
v_isSilent_boxed_1421_ = lean_unbox(v_isSilent_1414_);
v_res_1422_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1412_, v_severity_boxed_1420_, v_isSilent_boxed_1421_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
uint8_t v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = 2;
v___x_1432_ = 0;
v___x_1433_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1423_, v___x_1431_, v___x_1432_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1443_, size_t v_sz_1444_, size_t v_i_1445_, lean_object* v_b_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_usize_dec_lt(v_i_1445_, v_sz_1444_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_b_1446_);
return v___x_1455_;
}
else
{
lean_object* v_a_1456_; lean_object* v_snd_1457_; lean_object* v_snd_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_a_1456_ = lean_array_uget_borrowed(v_as_1443_, v_i_1445_);
v_snd_1457_ = lean_ctor_get(v_a_1456_, 1);
v_snd_1458_ = lean_ctor_get(v_snd_1457_, 1);
v___x_1459_ = lean_box(0);
lean_inc(v_snd_1458_);
v___x_1460_ = l_Lean_Parser_Error_toString(v_snd_1458_);
v___x_1461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
v___x_1462_ = l_Lean_MessageData_ofFormat(v___x_1461_);
v___x_1463_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1462_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1463_) == 0)
{
size_t v___x_1464_; size_t v___x_1465_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1445_, v___x_1464_);
v_i_1445_ = v___x_1465_;
v_b_1446_ = v___x_1459_;
goto _start;
}
else
{
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1467_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v_as_1467_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1498_, lean_object* v_binders_1499_, lean_object* v_docComment_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v_toCold_1509_; lean_object* v_env_1510_; lean_object* v_fileName_1511_; lean_object* v_options_1512_; lean_object* v_currNamespace_1513_; lean_object* v_openDecls_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1508_ = lean_st_ref_get(v_a_1506_);
v_toCold_1509_ = lean_ctor_get(v_a_1505_, 0);
v_env_1510_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_ref_n(v_env_1510_, 2);
lean_dec(v___x_1508_);
v_fileName_1511_ = lean_ctor_get(v_toCold_1509_, 0);
v_options_1512_ = lean_ctor_get(v_toCold_1509_, 2);
v_currNamespace_1513_ = lean_ctor_get(v_toCold_1509_, 4);
v_openDecls_1514_ = lean_ctor_get(v_toCold_1509_, 5);
v___x_1515_ = lean_string_utf8_byte_size(v_docComment_1500_);
lean_inc_ref_n(v_docComment_1500_, 2);
v___x_1516_ = l_Lean_FileMap_ofString(v_docComment_1500_);
lean_inc_ref(v___x_1516_);
lean_inc_ref(v_fileName_1511_);
v___x_1517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1517_, 0, v_docComment_1500_);
lean_ctor_set(v___x_1517_, 1, v_fileName_1511_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
lean_ctor_set(v___x_1517_, 3, v___x_1515_);
lean_inc(v_openDecls_1514_);
lean_inc(v_currNamespace_1513_);
lean_inc_ref(v_options_1512_);
v___x_1518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1518_, 0, v_env_1510_);
lean_ctor_set(v___x_1518_, 1, v_options_1512_);
lean_ctor_set(v___x_1518_, 2, v_currNamespace_1513_);
lean_ctor_set(v___x_1518_, 3, v_openDecls_1514_);
v___x_1519_ = l_Lean_Parser_mkParserState(v_docComment_1500_);
lean_dec_ref(v_docComment_1500_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1522_ = l_Lean_Parser_getTokenTable(v_env_1510_);
v___x_1523_ = l_Lean_Parser_ParserFn_run(v___x_1521_, v___x_1517_, v___x_1518_, v___x_1522_, v___x_1519_);
lean_inc_ref(v___x_1523_);
v___x_1524_ = l_Lean_Parser_ParserState_allErrors(v___x_1523_);
v___x_1525_ = lean_array_get_size(v___x_1524_);
v___x_1526_ = lean_nat_dec_eq(v___x_1525_, v___x_1520_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; size_t v_sz_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v___x_1523_);
lean_dec_ref(v___x_1516_);
lean_dec(v_binders_1499_);
lean_dec(v_declName_1498_);
v___x_1527_ = lean_box(0);
v_sz_1528_ = lean_array_size(v___x_1524_);
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1524_, v_sz_1528_, v___x_1529_, v___x_1527_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
lean_dec_ref(v___x_1524_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1530_, 0);
lean_dec(v_unused_1539_);
v___x_1532_ = v___x_1530_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v___x_1530_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1530_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1530_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_stxStack_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v___x_1524_);
v_stxStack_1548_ = lean_ctor_get(v___x_1523_, 0);
lean_inc_ref(v_stxStack_1548_);
lean_dec_ref(v___x_1523_);
v___x_1549_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1548_);
lean_dec_ref(v_stxStack_1548_);
v___x_1550_ = l_Lean_Syntax_getArgs(v___x_1549_);
lean_dec(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1516_);
v___x_1552_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1498_, v_binders_1499_, v___x_1550_, v___x_1551_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1553_, lean_object* v_binders_1554_, lean_object* v_docComment_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_versoDocStringOfText(v_declName_1553_, v_binders_1554_, v_docComment_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1564_, uint8_t v_severity_1565_, uint8_t v_isSilent_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1564_, v_severity_1565_, v_isSilent_1566_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1575_, lean_object* v_severity_1576_, lean_object* v_isSilent_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v_severity_boxed_1585_; uint8_t v_isSilent_boxed_1586_; lean_object* v_res_1587_; 
v_severity_boxed_1585_ = lean_unbox(v_severity_1576_);
v_isSilent_boxed_1586_ = lean_unbox(v_isSilent_1577_);
v_res_1587_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1575_, v_severity_boxed_1585_, v_isSilent_boxed_1586_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_bs_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1591_ == 0)
{
return v_bs_1590_;
}
else
{
lean_object* v_v_1592_; lean_object* v___x_1593_; lean_object* v_bs_x27_1594_; size_t v___x_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v_v_1592_ = lean_array_uget(v_bs_1590_, v_i_1589_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v_bs_x27_1594_ = lean_array_uset(v_bs_1590_, v_i_1589_, v___x_1593_);
v___x_1595_ = ((size_t)1ULL);
v___x_1596_ = lean_usize_add(v_i_1589_, v___x_1595_);
v___x_1597_ = lean_array_uset(v_bs_x27_1594_, v_i_1589_, v_v_1592_);
v_i_1589_ = v___x_1596_;
v_bs_1590_ = v___x_1597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1___boxed(lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_bs_1601_){
_start:
{
size_t v_sz_boxed_1602_; size_t v_i_boxed_1603_; lean_object* v_res_1604_; 
v_sz_boxed_1602_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_boxed_1602_, v_i_boxed_1603_, v_bs_1601_);
return v_res_1604_;
}
}
LEAN_EXPORT uint8_t l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(uint8_t v_suppressElabErrors_1605_, uint8_t v___x_1606_, lean_object* v_x_1607_){
_start:
{
if (lean_obj_tag(v_x_1607_) == 1)
{
lean_object* v_pre_1608_; 
v_pre_1608_ = lean_ctor_get(v_x_1607_, 0);
switch(lean_obj_tag(v_pre_1608_))
{
case 1:
{
lean_object* v_pre_1609_; 
v_pre_1609_ = lean_ctor_get(v_pre_1608_, 0);
switch(lean_obj_tag(v_pre_1609_))
{
case 0:
{
lean_object* v_str_1610_; lean_object* v_str_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_str_1610_ = lean_ctor_get(v_x_1607_, 1);
v_str_1611_ = lean_ctor_get(v_pre_1608_, 1);
v___x_1612_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1613_ = lean_string_dec_eq(v_str_1611_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1615_ = lean_string_dec_eq(v_str_1611_, v___x_1614_);
if (v___x_1615_ == 0)
{
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1617_ = lean_string_dec_eq(v_str_1610_, v___x_1616_);
if (v___x_1617_ == 0)
{
return v___x_1617_;
}
else
{
return v_suppressElabErrors_1605_;
}
}
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1619_ = lean_string_dec_eq(v_str_1610_, v___x_1618_);
if (v___x_1619_ == 0)
{
return v___x_1619_;
}
else
{
return v_suppressElabErrors_1605_;
}
}
}
case 1:
{
lean_object* v_pre_1620_; 
v_pre_1620_ = lean_ctor_get(v_pre_1609_, 0);
if (lean_obj_tag(v_pre_1620_) == 0)
{
lean_object* v_str_1621_; lean_object* v_str_1622_; lean_object* v_str_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_str_1621_ = lean_ctor_get(v_x_1607_, 1);
v_str_1622_ = lean_ctor_get(v_pre_1608_, 1);
v_str_1623_ = lean_ctor_get(v_pre_1609_, 1);
v___x_1624_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1625_ = lean_string_dec_eq(v_str_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1627_ = lean_string_dec_eq(v_str_1622_, v___x_1626_);
if (v___x_1627_ == 0)
{
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1629_ = lean_string_dec_eq(v_str_1621_, v___x_1628_);
if (v___x_1629_ == 0)
{
return v___x_1629_;
}
else
{
return v_suppressElabErrors_1605_;
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
lean_object* v_str_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v_str_1630_ = lean_ctor_get(v_x_1607_, 1);
v___x_1631_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1632_ = lean_string_dec_eq(v_str_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
return v___x_1632_;
}
else
{
return v_suppressElabErrors_1605_;
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
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1633_, lean_object* v___x_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1636_; uint8_t v___x_11313__boxed_1637_; uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_suppressElabErrors_boxed_1636_ = lean_unbox(v_suppressElabErrors_1633_);
v___x_11313__boxed_1637_ = lean_unbox(v___x_1634_);
v_res_1638_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0(v_suppressElabErrors_boxed_1636_, v___x_11313__boxed_1637_, v_x_1635_);
lean_dec(v_x_1635_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(uint8_t v_suppressElabErrors_1640_, uint8_t v___x_1641_, lean_object* v_x_1642_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 1)
{
lean_object* v_pre_1643_; 
v_pre_1643_ = lean_ctor_get(v_x_1642_, 0);
switch(lean_obj_tag(v_pre_1643_))
{
case 1:
{
lean_object* v_pre_1644_; 
v_pre_1644_ = lean_ctor_get(v_pre_1643_, 0);
switch(lean_obj_tag(v_pre_1644_))
{
case 0:
{
lean_object* v_str_1645_; lean_object* v_str_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_str_1645_ = lean_ctor_get(v_x_1642_, 1);
v_str_1646_ = lean_ctor_get(v_pre_1643_, 1);
v___x_1647_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__0));
v___x_1648_ = lean_string_dec_eq(v_str_1646_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__1));
v___x_1650_ = lean_string_dec_eq(v_str_1646_, v___x_1649_);
if (v___x_1650_ == 0)
{
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__2));
v___x_1652_ = lean_string_dec_eq(v_str_1645_, v___x_1651_);
if (v___x_1652_ == 0)
{
return v___x_1652_;
}
else
{
return v_suppressElabErrors_1640_;
}
}
}
else
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__3));
v___x_1654_ = lean_string_dec_eq(v_str_1645_, v___x_1653_);
if (v___x_1654_ == 0)
{
return v___x_1654_;
}
else
{
return v_suppressElabErrors_1640_;
}
}
}
case 1:
{
lean_object* v_pre_1655_; 
v_pre_1655_ = lean_ctor_get(v_pre_1644_, 0);
if (lean_obj_tag(v_pre_1655_) == 0)
{
lean_object* v_str_1656_; lean_object* v_str_1657_; lean_object* v_str_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_str_1656_ = lean_ctor_get(v_x_1642_, 1);
v_str_1657_ = lean_ctor_get(v_pre_1643_, 1);
v_str_1658_ = lean_ctor_get(v_pre_1644_, 1);
v___x_1659_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__4));
v___x_1660_ = lean_string_dec_eq(v_str_1658_, v___x_1659_);
if (v___x_1660_ == 0)
{
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__5));
v___x_1662_ = lean_string_dec_eq(v_str_1657_, v___x_1661_);
if (v___x_1662_ == 0)
{
return v___x_1662_;
}
else
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__6));
v___x_1664_ = lean_string_dec_eq(v_str_1656_, v___x_1663_);
if (v___x_1664_ == 0)
{
return v___x_1664_;
}
else
{
return v_suppressElabErrors_1640_;
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
lean_object* v_str_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_str_1665_ = lean_ctor_get(v_x_1642_, 1);
v___x_1666_ = ((lean_object*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___closed__7));
v___x_1667_ = lean_string_dec_eq(v_str_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
return v___x_1667_;
}
else
{
return v_suppressElabErrors_1640_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_1668_, lean_object* v___x_1669_, lean_object* v_x_1670_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1671_; uint8_t v___x_11377__boxed_1672_; uint8_t v_res_1673_; lean_object* v_r_1674_; 
v_suppressElabErrors_boxed_1671_ = lean_unbox(v_suppressElabErrors_1668_);
v___x_11377__boxed_1672_ = lean_unbox(v___x_1669_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0(v_suppressElabErrors_boxed_1671_, v___x_11377__boxed_1672_, v_x_1670_);
lean_dec(v_x_1670_);
v_r_1674_ = lean_box(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(lean_object* v___x_1675_, lean_object* v___x_1676_, lean_object* v_as_1677_, size_t v_sz_1678_, size_t v_i_1679_, lean_object* v_b_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_a_1685_; uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_lt(v_i_1679_, v_sz_1678_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___x_1675_);
v___x_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_b_1680_);
return v___x_1690_;
}
else
{
lean_object* v_a_1691_; lean_object* v_snd_1692_; lean_object* v_toCold_1693_; lean_object* v_fst_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1752_; 
v_a_1691_ = lean_array_uget(v_as_1677_, v_i_1679_);
v_snd_1692_ = lean_ctor_get(v_a_1691_, 1);
lean_inc(v_snd_1692_);
v_toCold_1693_ = lean_ctor_get(v___y_1681_, 0);
v_fst_1694_ = lean_ctor_get(v_a_1691_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v_a_1691_, 1);
lean_dec(v_unused_1753_);
v___x_1696_ = v_a_1691_;
v_isShared_1697_ = v_isSharedCheck_1752_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_fst_1694_);
lean_dec(v_a_1691_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1752_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1750_; 
v_snd_1698_ = lean_ctor_get(v_snd_1692_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_snd_1692_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v_snd_1692_, 0);
lean_dec(v_unused_1751_);
v___x_1700_ = v_snd_1692_;
v_isShared_1701_ = v_isSharedCheck_1750_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_dec(v_snd_1692_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1750_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint8_t v_suppressElabErrors_1702_; lean_object* v_fileName_1703_; lean_object* v_currNamespace_1704_; lean_object* v_openDecls_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_currNamespace_1717_; lean_object* v_openDecls_1718_; lean_object* v___y_1719_; 
v_suppressElabErrors_1702_ = lean_ctor_get_uint8(v___y_1681_, sizeof(void*)*3 + 1);
v_fileName_1703_ = lean_ctor_get(v_toCold_1693_, 0);
v_currNamespace_1704_ = lean_ctor_get(v_toCold_1693_, 4);
v_openDecls_1705_ = lean_ctor_get(v_toCold_1693_, 5);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_unsigned_to_nat(0u);
v___x_1708_ = lean_nat_dec_eq(v___x_1676_, v___x_1707_);
lean_inc_ref(v___x_1675_);
v___x_1709_ = l_Lean_FileMap_toPosition(v___x_1675_, v_fst_1694_);
lean_dec(v_fst_1694_);
v___x_1710_ = lean_box(0);
v___x_1711_ = 2;
v___x_1712_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1713_ = l_Lean_Parser_Error_toString(v_snd_1698_);
v___x_1714_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
v___x_1715_ = l_Lean_MessageData_ofFormat(v___x_1714_);
if (v_suppressElabErrors_1702_ == 0)
{
v_currNamespace_1717_ = v_currNamespace_1704_;
v_openDecls_1718_ = v_openDecls_1705_;
v___y_1719_ = v___y_1682_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; uint8_t v___x_1749_; 
v___x_1746_ = lean_box(v_suppressElabErrors_1702_);
v___x_1747_ = lean_box(v___x_1708_);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1748_, 0, v___x_1746_);
lean_closure_set(v___f_1748_, 1, v___x_1747_);
lean_inc_ref(v___x_1715_);
v___x_1749_ = l_Lean_MessageData_hasTag(v___f_1748_, v___x_1715_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v___x_1715_);
lean_dec_ref(v___x_1709_);
lean_del_object(v___x_1700_);
lean_del_object(v___x_1696_);
v_a_1685_ = v___x_1706_;
goto v___jp_1684_;
}
else
{
v_currNamespace_1717_ = v_currNamespace_1704_;
v_openDecls_1718_ = v_openDecls_1705_;
v___y_1719_ = v___y_1682_;
goto v___jp_1716_;
}
}
v___jp_1716_:
{
lean_object* v___x_1721_; 
lean_inc(v_openDecls_1718_);
lean_inc(v_currNamespace_1717_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v_openDecls_1718_);
lean_ctor_set(v___x_1700_, 0, v_currNamespace_1717_);
v___x_1721_ = v___x_1700_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_currNamespace_1717_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_openDecls_1718_);
v___x_1721_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 4);
lean_ctor_set(v___x_1696_, 1, v___x_1715_);
lean_ctor_set(v___x_1696_, 0, v___x_1721_);
v___x_1723_ = v___x_1696_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1715_);
v___x_1723_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v_nextMacroScope_1727_; lean_object* v_ngen_1728_; lean_object* v_auxDeclNGen_1729_; lean_object* v_traceState_1730_; lean_object* v_cache_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
lean_inc_ref(v_fileName_1703_);
v___x_1724_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1724_, 0, v_fileName_1703_);
lean_ctor_set(v___x_1724_, 1, v___x_1709_);
lean_ctor_set(v___x_1724_, 2, v___x_1710_);
lean_ctor_set(v___x_1724_, 3, v___x_1712_);
lean_ctor_set(v___x_1724_, 4, v___x_1723_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5, v___x_1708_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5 + 1, v___x_1711_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*5 + 2, v___x_1708_);
v___x_1725_ = lean_st_ref_take(v___y_1719_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
v_nextMacroScope_1727_ = lean_ctor_get(v___x_1725_, 1);
v_ngen_1728_ = lean_ctor_get(v___x_1725_, 2);
v_auxDeclNGen_1729_ = lean_ctor_get(v___x_1725_, 3);
v_traceState_1730_ = lean_ctor_get(v___x_1725_, 4);
v_cache_1731_ = lean_ctor_get(v___x_1725_, 5);
v_messages_1732_ = lean_ctor_get(v___x_1725_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1725_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1725_, 8);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v___x_1725_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_cache_1731_);
lean_inc(v_traceState_1730_);
lean_inc(v_auxDeclNGen_1729_);
lean_inc(v_ngen_1728_);
lean_inc(v_nextMacroScope_1727_);
lean_inc(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_MessageLog_add(v___x_1724_, v_messages_1732_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 6, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_env_1726_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_nextMacroScope_1727_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_ngen_1728_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_auxDeclNGen_1729_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v_traceState_1730_);
lean_ctor_set(v_reuseFailAlloc_1742_, 5, v_cache_1731_);
lean_ctor_set(v_reuseFailAlloc_1742_, 6, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 7, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1742_, 8, v_snapshotTasks_1734_);
v___x_1740_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_st_ref_put(v___y_1719_, v___x_1740_);
v_a_1685_ = v___x_1706_;
goto v___jp_1684_;
}
}
}
}
}
}
}
}
v___jp_1684_:
{
size_t v___x_1686_; size_t v___x_1687_; 
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1679_, v___x_1686_);
v_i_1679_ = v___x_1687_;
v_b_1680_ = v_a_1685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v_as_1756_, lean_object* v_sz_1757_, lean_object* v_i_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1757_);
lean_dec(v_sz_1757_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1758_);
lean_dec(v_i_1758_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_1754_, v___x_1755_, v_as_1756_, v_sz_boxed_1763_, v_i_boxed_1764_, v_b_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec_ref(v_as_1756_);
lean_dec(v___x_1755_);
return v_res_1765_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_box(1);
v___x_1767_ = l_Lean_MessageData_ofFormat(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__2));
v___x_1772_ = l_Lean_MessageData_ofFormat(v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
return v_x_1773_;
}
else
{
lean_object* v_head_1775_; lean_object* v_tail_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1798_; 
v_head_1775_ = lean_ctor_get(v_x_1774_, 0);
v_tail_1776_ = lean_ctor_get(v_x_1774_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_x_1774_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1778_ = v_x_1774_;
v_isShared_1779_ = v_isSharedCheck_1798_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_tail_1776_);
lean_inc(v_head_1775_);
lean_dec(v_x_1774_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1798_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_before_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1796_; 
v_before_1780_ = lean_ctor_get(v_head_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_head_1775_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_head_1775_, 1);
lean_dec(v_unused_1797_);
v___x_1782_ = v_head_1775_;
v_isShared_1783_ = v_isSharedCheck_1796_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_before_1780_);
lean_dec(v_head_1775_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1796_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 7);
lean_ctor_set(v___x_1782_, 1, v___x_1784_);
lean_ctor_set(v___x_1782_, 0, v_x_1773_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_x_1773_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1787_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__3);
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 7);
lean_ctor_set(v___x_1778_, 1, v___x_1787_);
lean_ctor_set(v___x_1778_, 0, v___x_1786_);
v___x_1789_ = v___x_1778_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = l_Lean_MessageData_ofSyntax(v_before_1780_);
v___x_1791_ = l_Lean_indentD(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v_x_1773_ = v___x_1792_;
v_x_1774_ = v_tail_1776_;
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
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__1));
v___x_1803_ = l_Lean_MessageData_ofFormat(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_1804_, lean_object* v_macroStack_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_toCold_1808_; lean_object* v_options_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_toCold_1808_ = lean_ctor_get(v___y_1806_, 0);
v_options_1809_ = lean_ctor_get(v_toCold_1808_, 2);
v___x_1810_ = l_Lean_Elab_pp_macroStack;
v___x_1811_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; 
lean_dec(v_macroStack_1805_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_msgData_1804_);
return v___x_1812_;
}
else
{
if (lean_obj_tag(v_macroStack_1805_) == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v_msgData_1804_);
return v___x_1813_;
}
else
{
lean_object* v_head_1814_; lean_object* v_after_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1830_; 
v_head_1814_ = lean_ctor_get(v_macroStack_1805_, 0);
lean_inc(v_head_1814_);
v_after_1815_ = lean_ctor_get(v_head_1814_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_head_1814_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v_head_1814_, 0);
lean_dec(v_unused_1831_);
v___x_1817_ = v_head_1814_;
v_isShared_1818_ = v_isSharedCheck_1830_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_after_1815_);
lean_dec(v_head_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1830_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5___closed__0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 7);
lean_ctor_set(v___x_1817_, 1, v___x_1819_);
lean_ctor_set(v___x_1817_, 0, v_msgData_1804_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_msgData_1804_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_msgData_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1822_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_MessageData_ofSyntax(v_after_1815_);
v___x_1825_ = l_Lean_indentD(v___x_1824_);
v_msgData_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1826_, 0, v___x_1823_);
lean_ctor_set(v_msgData_1826_, 1, v___x_1825_);
v___x_1827_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4_spec__5(v_msgData_1826_, v_macroStack_1805_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_1832_, lean_object* v_macroStack_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_1832_, v_macroStack_1833_, v___y_1834_);
lean_dec_ref(v___y_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_ref_1845_; lean_object* v_macroStack_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v_a_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_ref_1845_ = lean_ctor_get(v___y_1842_, 2);
v_macroStack_1846_ = lean_ctor_get(v___y_1838_, 1);
v___x_1847_ = l_Lean_Elab_getBetterRef(v_ref_1845_, v_macroStack_1846_);
v___x_1848_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_1837_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
lean_inc(v_macroStack_1846_);
v___x_1850_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_a_1849_, v_macroStack_1846_, v___y_1842_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1847_);
lean_ctor_set(v___x_1855_, 1, v_a_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
lean_ctor_set(v___x_1853_, 0, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(lean_object* v_ref_1869_, lean_object* v_msg_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_toCold_1878_; lean_object* v_currRecDepth_1879_; lean_object* v_ref_1880_; uint8_t v_diag_1881_; uint8_t v_suppressElabErrors_1882_; lean_object* v_ref_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_toCold_1878_ = lean_ctor_get(v___y_1875_, 0);
v_currRecDepth_1879_ = lean_ctor_get(v___y_1875_, 1);
v_ref_1880_ = lean_ctor_get(v___y_1875_, 2);
v_diag_1881_ = lean_ctor_get_uint8(v___y_1875_, sizeof(void*)*3);
v_suppressElabErrors_1882_ = lean_ctor_get_uint8(v___y_1875_, sizeof(void*)*3 + 1);
v_ref_1883_ = l_Lean_replaceRef(v_ref_1869_, v_ref_1880_);
lean_inc(v_currRecDepth_1879_);
lean_inc_ref(v_toCold_1878_);
v___x_1884_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1884_, 0, v_toCold_1878_);
lean_ctor_set(v___x_1884_, 1, v_currRecDepth_1879_);
lean_ctor_set(v___x_1884_, 2, v_ref_1883_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*3, v_diag_1881_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*3 + 1, v_suppressElabErrors_1882_);
v___x_1885_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___x_1884_, v___y_1876_);
lean_dec_ref_known(v___x_1884_, 3);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_1886_, v_msg_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v_ref_1886_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(lean_object* v_docComment_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
uint8_t v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_currNamespace_1915_; lean_object* v_openDecls_1916_; lean_object* v___y_1917_; uint8_t v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; uint8_t v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1998_; uint8_t v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; uint8_t v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
lean_inc(v_docComment_1896_);
v___x_2058_ = l_Lean_Syntax_getKind(v_docComment_1896_);
v___x_2059_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_2060_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_2061_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_2062_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__4));
v___x_2063_ = lean_name_eq(v___x_2058_, v___x_2062_);
lean_dec(v___x_2058_);
if (v___x_2063_ == 0)
{
goto v___jp_2034_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_Lean_Syntax_getArg(v_docComment_1896_, v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_kind_2066_; 
v_kind_2066_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_kind_2066_);
if (lean_obj_tag(v_kind_2066_) == 1)
{
lean_object* v_pre_2067_; 
v_pre_2067_ = lean_ctor_get(v_kind_2066_, 0);
lean_inc(v_pre_2067_);
if (lean_obj_tag(v_pre_2067_) == 1)
{
lean_object* v_pre_2068_; 
v_pre_2068_ = lean_ctor_get(v_pre_2067_, 0);
lean_inc(v_pre_2068_);
if (lean_obj_tag(v_pre_2068_) == 1)
{
lean_object* v_pre_2069_; 
v_pre_2069_ = lean_ctor_get(v_pre_2068_, 0);
lean_inc(v_pre_2069_);
if (lean_obj_tag(v_pre_2069_) == 1)
{
lean_object* v_pre_2070_; 
v_pre_2070_ = lean_ctor_get(v_pre_2069_, 0);
lean_inc(v_pre_2070_);
if (lean_obj_tag(v_pre_2070_) == 0)
{
lean_object* v_info_2071_; lean_object* v_args_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2096_; 
v_info_2071_ = lean_ctor_get(v___x_2065_, 0);
v_args_2072_ = lean_ctor_get(v___x_2065_, 2);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v___x_2065_, 1);
lean_dec(v_unused_2097_);
v___x_2074_ = v___x_2065_;
v_isShared_2075_ = v_isSharedCheck_2096_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_args_2072_);
lean_inc(v_info_2071_);
lean_dec(v___x_2065_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2096_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_str_2076_; lean_object* v_str_2077_; lean_object* v_str_2078_; lean_object* v_str_2079_; uint8_t v___x_2080_; 
v_str_2076_ = lean_ctor_get(v_kind_2066_, 1);
lean_inc_ref(v_str_2076_);
lean_dec_ref_known(v_kind_2066_, 2);
v_str_2077_ = lean_ctor_get(v_pre_2067_, 1);
lean_inc_ref(v_str_2077_);
lean_dec_ref_known(v_pre_2067_, 2);
v_str_2078_ = lean_ctor_get(v_pre_2068_, 1);
lean_inc_ref(v_str_2078_);
lean_dec_ref_known(v_pre_2068_, 2);
v_str_2079_ = lean_ctor_get(v_pre_2069_, 1);
lean_inc_ref(v_str_2079_);
lean_dec_ref_known(v_pre_2069_, 2);
v___x_2080_ = lean_string_dec_eq(v_str_2079_, v___x_2059_);
lean_dec_ref(v_str_2079_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v_str_2078_);
lean_dec_ref(v_str_2077_);
lean_dec_ref(v_str_2076_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_args_2072_);
lean_dec(v_info_2071_);
goto v___jp_2034_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_string_dec_eq(v_str_2078_, v___x_2060_);
lean_dec_ref(v_str_2078_);
if (v___x_2081_ == 0)
{
lean_dec_ref(v_str_2077_);
lean_dec_ref(v_str_2076_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_args_2072_);
lean_dec(v_info_2071_);
goto v___jp_2034_;
}
else
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_string_dec_eq(v_str_2077_, v___x_2061_);
lean_dec_ref(v_str_2077_);
if (v___x_2082_ == 0)
{
lean_dec_ref(v_str_2076_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_args_2072_);
lean_dec(v_info_2071_);
goto v___jp_2034_;
}
else
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_2084_ = lean_string_dec_eq(v_str_2076_, v___x_2083_);
lean_dec_ref(v_str_2076_);
if (v___x_2084_ == 0)
{
lean_del_object(v___x_2074_);
lean_dec_ref(v_args_2072_);
lean_dec(v_info_2071_);
goto v___jp_2034_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_dec(v_docComment_1896_);
v___x_2085_ = l_Lean_Name_str___override(v_pre_2070_, v___x_2059_);
v___x_2086_ = l_Lean_Name_str___override(v___x_2085_, v___x_2060_);
v___x_2087_ = l_Lean_Name_str___override(v___x_2086_, v___x_2061_);
v___x_2088_ = l_Lean_Name_str___override(v___x_2087_, v___x_2083_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2088_);
v___x_2090_ = v___x_2074_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_info_2071_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_args_2072_);
v___x_2090_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2091_ = lean_unsigned_to_nat(1u);
v___x_2092_ = l_Lean_Syntax_getArg(v___x_2090_, v___x_2091_);
lean_dec_ref(v___x_2090_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2069_, 2);
lean_dec(v_pre_2070_);
lean_dec_ref_known(v_pre_2068_, 2);
lean_dec_ref_known(v_pre_2067_, 2);
lean_dec_ref_known(v_kind_2066_, 2);
lean_dec_ref_known(v___x_2065_, 3);
goto v___jp_2034_;
}
}
else
{
lean_dec(v_pre_2069_);
lean_dec_ref_known(v_pre_2068_, 2);
lean_dec_ref_known(v_pre_2067_, 2);
lean_dec_ref_known(v_kind_2066_, 2);
lean_dec_ref_known(v___x_2065_, 3);
goto v___jp_2034_;
}
}
else
{
lean_dec(v_pre_2068_);
lean_dec_ref_known(v_pre_2067_, 2);
lean_dec_ref_known(v_kind_2066_, 2);
lean_dec_ref_known(v___x_2065_, 3);
goto v___jp_2034_;
}
}
else
{
lean_dec_ref_known(v_kind_2066_, 2);
lean_dec(v_pre_2067_);
lean_dec_ref_known(v___x_2065_, 3);
goto v___jp_2034_;
}
}
else
{
lean_dec_ref_known(v___x_2065_, 3);
lean_dec(v_kind_2066_);
goto v___jp_2034_;
}
}
else
{
lean_dec(v___x_2065_);
goto v___jp_2034_;
}
}
v___jp_1904_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
return v___x_1906_;
}
v___jp_1907_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_env_1922_; lean_object* v_nextMacroScope_1923_; lean_object* v_ngen_1924_; lean_object* v_auxDeclNGen_1925_; lean_object* v_traceState_1926_; lean_object* v_cache_1927_; lean_object* v_messages_1928_; lean_object* v_infoState_1929_; lean_object* v_snapshotTasks_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1939_; 
lean_inc(v_openDecls_1916_);
lean_inc(v_currNamespace_1915_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_currNamespace_1915_);
lean_ctor_set(v___x_1918_, 1, v_openDecls_1916_);
v___x_1919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___y_1910_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1909_);
v___x_1920_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1920_, 0, v___y_1909_);
lean_ctor_set(v___x_1920_, 1, v___y_1914_);
lean_ctor_set(v___x_1920_, 2, v___y_1913_);
lean_ctor_set(v___x_1920_, 3, v___y_1911_);
lean_ctor_set(v___x_1920_, 4, v___x_1919_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*5, v___y_1912_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*5 + 1, v___y_1908_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*5 + 2, v___y_1912_);
v___x_1921_ = lean_st_ref_take(v___y_1917_);
v_env_1922_ = lean_ctor_get(v___x_1921_, 0);
v_nextMacroScope_1923_ = lean_ctor_get(v___x_1921_, 1);
v_ngen_1924_ = lean_ctor_get(v___x_1921_, 2);
v_auxDeclNGen_1925_ = lean_ctor_get(v___x_1921_, 3);
v_traceState_1926_ = lean_ctor_get(v___x_1921_, 4);
v_cache_1927_ = lean_ctor_get(v___x_1921_, 5);
v_messages_1928_ = lean_ctor_get(v___x_1921_, 6);
v_infoState_1929_ = lean_ctor_get(v___x_1921_, 7);
v_snapshotTasks_1930_ = lean_ctor_get(v___x_1921_, 8);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1932_ = v___x_1921_;
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snapshotTasks_1930_);
lean_inc(v_infoState_1929_);
lean_inc(v_messages_1928_);
lean_inc(v_cache_1927_);
lean_inc(v_traceState_1926_);
lean_inc(v_auxDeclNGen_1925_);
lean_inc(v_ngen_1924_);
lean_inc(v_nextMacroScope_1923_);
lean_inc(v_env_1922_);
lean_dec(v___x_1921_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = l_Lean_MessageLog_add(v___x_1920_, v_messages_1928_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 6, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_env_1922_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_nextMacroScope_1923_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_ngen_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_auxDeclNGen_1925_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_traceState_1926_);
lean_ctor_set(v_reuseFailAlloc_1938_, 5, v_cache_1927_);
lean_ctor_set(v_reuseFailAlloc_1938_, 6, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1938_, 7, v_infoState_1929_);
lean_ctor_set(v_reuseFailAlloc_1938_, 8, v_snapshotTasks_1930_);
v___x_1936_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_st_ref_put(v___y_1917_, v___x_1936_);
goto v___jp_1904_;
}
}
}
v___jp_1940_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
lean_inc_ref(v___y_1949_);
v___x_1950_ = l_Lean_Parser_ParserState_allErrors(v___y_1949_);
v___x_1951_ = lean_array_get_size(v___x_1950_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_nat_dec_eq(v___x_1951_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; size_t v_sz_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
lean_dec_ref(v___y_1949_);
lean_dec_ref(v___y_1948_);
v___x_1954_ = lean_box(0);
v_sz_1955_ = lean_array_size(v___x_1950_);
v___x_1956_ = ((size_t)0ULL);
lean_inc_ref(v___y_1947_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___y_1947_, v___x_1951_, v___x_1950_, v_sz_1955_, v___x_1956_, v___x_1954_, v___y_1901_, v___y_1902_);
lean_dec_ref(v___x_1950_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; 
v_unused_1966_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1966_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_box(0);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1957_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1957_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_stxStack_1975_; lean_object* v_pos_1976_; uint8_t v___x_1977_; 
lean_dec_ref(v___x_1950_);
v_stxStack_1975_ = lean_ctor_get(v___y_1949_, 0);
lean_inc_ref(v_stxStack_1975_);
v_pos_1976_ = lean_ctor_get(v___y_1949_, 2);
lean_inc(v_pos_1976_);
lean_dec_ref(v___y_1949_);
v___x_1977_ = l_Lean_Parser_InputContext_atEnd(v___y_1948_, v_pos_1976_);
lean_dec_ref(v___y_1948_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint32_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec_ref(v_stxStack_1975_);
lean_inc_ref(v___y_1947_);
v___x_1978_ = l_Lean_FileMap_toPosition(v___y_1947_, v_pos_1976_);
v___x_1979_ = lean_box(0);
v___x_1980_ = 2;
v___x_1981_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__3___closed__0));
v___x_1982_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__0));
v___x_1983_ = lean_string_utf8_get(v___y_1945_, v_pos_1976_);
lean_dec(v_pos_1976_);
v___x_1984_ = lean_string_push(v___x_1981_, v___x_1983_);
v___x_1985_ = lean_string_append(v___x_1982_, v___x_1984_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___lam__5___closed__1));
v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v___x_1989_ = l_Lean_MessageData_ofFormat(v___x_1988_);
if (v___y_1946_ == 0)
{
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1944_;
v___y_1910_ = v___x_1989_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___x_1977_;
v___y_1913_ = v___x_1979_;
v___y_1914_ = v___x_1978_;
v_currNamespace_1915_ = v___y_1942_;
v_openDecls_1916_ = v___y_1943_;
v___y_1917_ = v___y_1902_;
goto v___jp_1907_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; uint8_t v___x_1993_; 
v___x_1990_ = lean_box(v___y_1941_);
v___x_1991_ = lean_box(v___x_1977_);
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1992_, 0, v___x_1990_);
lean_closure_set(v___f_1992_, 1, v___x_1991_);
lean_inc_ref(v___x_1989_);
v___x_1993_ = l_Lean_MessageData_hasTag(v___f_1992_, v___x_1989_);
if (v___x_1993_ == 0)
{
lean_dec_ref(v___x_1989_);
lean_dec_ref(v___x_1978_);
goto v___jp_1904_;
}
else
{
v___y_1908_ = v___x_1980_;
v___y_1909_ = v___y_1944_;
v___y_1910_ = v___x_1989_;
v___y_1911_ = v___x_1981_;
v___y_1912_ = v___x_1977_;
v___y_1913_ = v___x_1979_;
v___y_1914_ = v___x_1978_;
v_currNamespace_1915_ = v___y_1942_;
v_openDecls_1916_ = v___y_1943_;
v___y_1917_ = v___y_1902_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec(v_pos_1976_);
v___x_1994_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1975_);
lean_dec_ref(v_stxStack_1975_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
return v___x_1996_;
}
}
}
v___jp_1997_:
{
lean_object* v___x_2011_; lean_object* v_env_2012_; lean_object* v_ictx_2013_; lean_object* v_pmctx_2014_; lean_object* v_blockCtxt_2015_; lean_object* v___x_2016_; lean_object* v_s_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_s_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2011_ = lean_st_ref_get(v___y_1902_);
v_env_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc_ref_n(v_env_2012_, 2);
lean_dec(v___x_2011_);
lean_inc(v___y_2010_);
lean_inc_ref_n(v___y_2007_, 2);
lean_inc_ref(v___y_2003_);
lean_inc_ref(v___y_1998_);
v_ictx_2013_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_ictx_2013_, 0, v___y_1998_);
lean_ctor_set(v_ictx_2013_, 1, v___y_2003_);
lean_ctor_set(v_ictx_2013_, 2, v___y_2007_);
lean_ctor_set(v_ictx_2013_, 3, v___y_2010_);
lean_inc(v___y_2009_);
lean_inc(v___y_2008_);
lean_inc_ref(v___y_2002_);
v_pmctx_2014_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_pmctx_2014_, 0, v_env_2012_);
lean_ctor_set(v_pmctx_2014_, 1, v___y_2002_);
lean_ctor_set(v_pmctx_2014_, 2, v___y_2008_);
lean_ctor_set(v_pmctx_2014_, 3, v___y_2009_);
lean_inc(v___y_2005_);
v_blockCtxt_2015_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v___y_2007_, v___y_2005_, v___y_2010_);
v___x_2016_ = l_Lean_Parser_mkParserState(v___y_1998_);
lean_inc_ref(v___x_2016_);
v_s_2017_ = l_Lean_Parser_ParserState_setPos(v___x_2016_, v___y_2005_);
v___x_2018_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document), 3, 1);
lean_closure_set(v___x_2018_, 0, v_blockCtxt_2015_);
v___x_2019_ = l_Lean_Parser_getTokenTable(v_env_2012_);
lean_inc_ref(v___x_2019_);
lean_inc_ref(v_pmctx_2014_);
lean_inc_ref(v_ictx_2013_);
v_s_2020_ = l_Lean_Parser_ParserFn_run(v___x_2018_, v_ictx_2013_, v_pmctx_2014_, v___x_2019_, v_s_2017_);
lean_inc_ref(v_s_2020_);
v___x_2021_ = l_Lean_Parser_ParserState_allErrors(v_s_2020_);
v___x_2022_ = lean_array_get_size(v___x_2021_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_nat_dec_eq(v___x_2022_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v___x_2019_);
lean_dec_ref(v___x_2016_);
lean_dec_ref_known(v_pmctx_2014_, 4);
lean_dec(v___y_2004_);
v___y_1941_ = v___y_1999_;
v___y_1942_ = v___y_2000_;
v___y_1943_ = v___y_2001_;
v___y_1944_ = v___y_2003_;
v___y_1945_ = v___y_1998_;
v___y_1946_ = v___y_2006_;
v___y_1947_ = v___y_2007_;
v___y_1948_ = v_ictx_2013_;
v___y_1949_ = v_s_2020_;
goto v___jp_1940_;
}
else
{
lean_object* v_pos_2025_; uint8_t v___x_2026_; 
v_pos_2025_ = lean_ctor_get(v_s_2020_, 2);
lean_inc(v_pos_2025_);
v___x_2026_ = l_Lean_Parser_InputContext_atEnd(v_ictx_2013_, v_pos_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v_s_2020_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___y_2004_);
lean_ctor_set(v___x_2029_, 1, v___x_2023_);
v___x_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2023_);
lean_ctor_set(v___x_2030_, 1, v___x_2027_);
lean_ctor_set(v___x_2030_, 2, v___x_2028_);
lean_ctor_set(v___x_2030_, 3, v___x_2029_);
lean_ctor_set(v___x_2030_, 4, v___x_2023_);
v___x_2031_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_block), 3, 1);
lean_closure_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = l_Lean_Parser_ParserState_setPos(v___x_2016_, v_pos_2025_);
lean_inc_ref(v_ictx_2013_);
v___x_2033_ = l_Lean_Parser_ParserFn_run(v___x_2031_, v_ictx_2013_, v_pmctx_2014_, v___x_2019_, v___x_2032_);
v___y_1941_ = v___y_1999_;
v___y_1942_ = v___y_2000_;
v___y_1943_ = v___y_2001_;
v___y_1944_ = v___y_2003_;
v___y_1945_ = v___y_1998_;
v___y_1946_ = v___y_2006_;
v___y_1947_ = v___y_2007_;
v___y_1948_ = v_ictx_2013_;
v___y_1949_ = v___x_2033_;
goto v___jp_1940_;
}
else
{
lean_dec(v_pos_2025_);
lean_dec_ref(v___x_2019_);
lean_dec_ref(v___x_2016_);
lean_dec_ref_known(v_pmctx_2014_, 4);
lean_dec(v___y_2004_);
v___y_1941_ = v___y_1999_;
v___y_1942_ = v___y_2000_;
v___y_1943_ = v___y_2001_;
v___y_1944_ = v___y_2003_;
v___y_1945_ = v___y_1998_;
v___y_1946_ = v___y_2006_;
v___y_1947_ = v___y_2007_;
v___y_1948_ = v_ictx_2013_;
v___y_1949_ = v_s_2020_;
goto v___jp_1940_;
}
}
}
v___jp_2034_:
{
lean_object* v_toCold_2035_; uint8_t v_suppressElabErrors_2036_; lean_object* v_fileName_2037_; lean_object* v_fileMap_2038_; lean_object* v_options_2039_; lean_object* v_currNamespace_2040_; lean_object* v_openDecls_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
v_toCold_2035_ = lean_ctor_get(v___y_1901_, 0);
v_suppressElabErrors_2036_ = lean_ctor_get_uint8(v___y_1901_, sizeof(void*)*3 + 1);
v_fileName_2037_ = lean_ctor_get(v_toCold_2035_, 0);
v_fileMap_2038_ = lean_ctor_get(v_toCold_2035_, 1);
v_options_2039_ = lean_ctor_get(v_toCold_2035_, 2);
v_currNamespace_2040_ = lean_ctor_get(v_toCold_2035_, 4);
v_openDecls_2041_ = lean_ctor_get(v_toCold_2035_, 5);
v___x_2042_ = lean_unsigned_to_nat(1u);
v___x_2043_ = l_Lean_Syntax_getArg(v_docComment_1896_, v___x_2042_);
v___x_2044_ = 1;
v___x_2045_ = l_Lean_Syntax_getPos_x3f(v___x_2043_, v___x_2044_);
if (lean_obj_tag(v___x_2045_) == 1)
{
lean_object* v_val_2046_; lean_object* v___x_2047_; 
v_val_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_val_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = l_Lean_Syntax_getTailPos_x3f(v___x_2043_, v___x_2044_);
lean_dec(v___x_2043_);
if (lean_obj_tag(v___x_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v_source_2049_; lean_object* v___x_2050_; lean_object* v_endPos_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
lean_dec(v_docComment_1896_);
v_val_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v_source_2049_ = lean_ctor_get(v_fileMap_2038_, 0);
v___x_2050_ = lean_string_utf8_prev(v_source_2049_, v_val_2048_);
lean_dec(v_val_2048_);
v_endPos_2051_ = lean_string_utf8_prev(v_source_2049_, v___x_2050_);
lean_dec(v___x_2050_);
v___x_2052_ = lean_string_utf8_byte_size(v_source_2049_);
v___x_2053_ = lean_nat_dec_le(v_endPos_2051_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec(v_endPos_2051_);
v___y_1998_ = v_source_2049_;
v___y_1999_ = v_suppressElabErrors_2036_;
v___y_2000_ = v_currNamespace_2040_;
v___y_2001_ = v_openDecls_2041_;
v___y_2002_ = v_options_2039_;
v___y_2003_ = v_fileName_2037_;
v___y_2004_ = v___x_2042_;
v___y_2005_ = v_val_2046_;
v___y_2006_ = v_suppressElabErrors_2036_;
v___y_2007_ = v_fileMap_2038_;
v___y_2008_ = v_currNamespace_2040_;
v___y_2009_ = v_openDecls_2041_;
v___y_2010_ = v___x_2052_;
goto v___jp_1997_;
}
else
{
v___y_1998_ = v_source_2049_;
v___y_1999_ = v_suppressElabErrors_2036_;
v___y_2000_ = v_currNamespace_2040_;
v___y_2001_ = v_openDecls_2041_;
v___y_2002_ = v_options_2039_;
v___y_2003_ = v_fileName_2037_;
v___y_2004_ = v___x_2042_;
v___y_2005_ = v_val_2046_;
v___y_2006_ = v_suppressElabErrors_2036_;
v___y_2007_ = v_fileMap_2038_;
v___y_2008_ = v_currNamespace_2040_;
v___y_2009_ = v_openDecls_2041_;
v___y_2010_ = v_endPos_2051_;
goto v___jp_1997_;
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v___x_2047_);
lean_dec(v_val_2046_);
v___x_2054_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2055_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1896_, v___x_2054_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v_docComment_1896_);
return v___x_2055_;
}
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec(v___x_2045_);
lean_dec(v___x_2043_);
v___x_2056_ = lean_obj_once(&l_Lean_parseVersoDocString___redArg___lam__11___closed__1, &l_Lean_parseVersoDocString___redArg___lam__11___closed__1_once, _init_l_Lean_parseVersoDocString___redArg___lam__11___closed__1);
v___x_2057_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_docComment_1896_, v___x_2056_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
lean_dec(v_docComment_1896_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0___boxed(lean_object* v_docComment_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_2120_, lean_object* v_binders_2121_, lean_object* v_docComment_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v_body_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_unsigned_to_nat(1u);
v_body_2131_ = l_Lean_Syntax_getArg(v_docComment_2122_, v___x_2130_);
v___x_2132_ = 1;
v___x_2133_ = l_Lean_Syntax_getPos_x3f(v_body_2131_, v___x_2132_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
lean_inc(v_body_2131_);
v___x_2135_ = l_Lean_Syntax_isOfKind(v_body_2131_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v_body_2131_);
v___x_2136_ = l_Lean_TSyntax_getDocString(v_docComment_2122_);
lean_dec(v_docComment_2122_);
v___x_2137_ = l_Lean_versoDocStringOfText(v_declName_2120_, v_binders_2121_, v___x_2136_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
lean_dec(v_docComment_2122_);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = l_Lean_Syntax_getArg(v_body_2131_, v___x_2138_);
lean_dec(v_body_2131_);
v___x_2140_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
lean_inc(v___x_2139_);
v___x_2141_ = l_Lean_Syntax_isOfKind(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_Syntax_getArgs(v___x_2139_);
lean_dec(v___x_2139_);
v___x_2143_ = lean_box(0);
v___x_2144_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_2120_, v_binders_2121_, v___x_2142_, v___x_2143_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2144_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = l_Lean_Syntax_getArg(v___x_2139_, v___x_2138_);
lean_dec(v___x_2139_);
v___x_2146_ = l_Lean_Syntax_getAtomVal(v___x_2145_);
lean_dec(v___x_2145_);
v___x_2147_ = l_Lean_versoDocStringOfText(v_declName_2120_, v_binders_2121_, v___x_2146_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
return v___x_2147_;
}
}
}
else
{
lean_object* v___x_2148_; 
lean_dec_ref_known(v___x_2133_, 1);
lean_dec(v_body_2131_);
v___x_2148_ = l_Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0(v_docComment_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2199_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2199_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2199_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
if (lean_obj_tag(v_a_2149_) == 1)
{
lean_object* v_val_2153_; lean_object* v___x_2154_; size_t v_sz_2155_; size_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; 
lean_del_object(v___x_2151_);
v_val_2153_ = lean_ctor_get(v_a_2149_, 0);
lean_inc(v_val_2153_);
lean_dec_ref_known(v_a_2149_, 1);
v___x_2154_ = l_Lean_Syntax_getArgs(v_val_2153_);
lean_dec(v_val_2153_);
v_sz_2155_ = lean_array_size(v___x_2154_);
v___x_2156_ = ((size_t)0ULL);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_versoDocString_spec__1(v_sz_2155_, v___x_2156_, v___x_2154_);
v___x_2158_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_2158_, 0, v___x_2157_);
v___x_2159_ = 0;
v___x_2160_ = l_Lean_Doc_DocM_exec___redArg(v_declName_2120_, v_binders_2121_, v___x_2158_, v___x_2159_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2186_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2186_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2186_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_fst_2165_; lean_object* v_snd_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2185_; 
v_fst_2165_ = lean_ctor_get(v_a_2161_, 0);
v_snd_2166_ = lean_ctor_get(v_a_2161_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2168_ = v_a_2161_;
v_isShared_2169_ = v_isSharedCheck_2185_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_snd_2166_);
lean_inc(v_fst_2165_);
lean_dec(v_a_2161_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2185_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2184_; 
v_fst_2170_ = lean_ctor_get(v_fst_2165_, 0);
v_snd_2171_ = lean_ctor_get(v_fst_2165_, 1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_fst_2165_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2173_ = v_fst_2165_;
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_dec(v_fst_2165_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_fst_2170_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_snd_2171_);
v___x_2176_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
lean_object* v___x_2178_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2176_);
v___x_2178_ = v___x_2168_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_snd_2166_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2178_);
v___x_2180_ = v___x_2163_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
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
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
v_a_2187_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2160_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2160_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
lean_dec(v_a_2149_);
lean_dec(v_binders_2121_);
lean_dec(v_declName_2120_);
v___x_2195_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2195_);
v___x_2197_ = v___x_2151_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_binders_2121_);
lean_dec(v_declName_2120_);
v_a_2200_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2148_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2148_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_2208_, lean_object* v_binders_2209_, lean_object* v_docComment_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_versoDocString(v_declName_2208_, v_binders_2209_, v_docComment_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_a_2211_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(lean_object* v___x_2219_, lean_object* v___x_2220_, lean_object* v_as_2221_, size_t v_sz_2222_, size_t v_i_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___redArg(v___x_2219_, v___x_2220_, v_as_2221_, v_sz_2222_, v_i_2223_, v_b_2224_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0___boxed(lean_object* v___x_2233_, lean_object* v___x_2234_, lean_object* v_as_2235_, lean_object* v_sz_2236_, lean_object* v_i_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
size_t v_sz_boxed_2246_; size_t v_i_boxed_2247_; lean_object* v_res_2248_; 
v_sz_boxed_2246_ = lean_unbox_usize(v_sz_2236_);
lean_dec(v_sz_2236_);
v_i_boxed_2247_ = lean_unbox_usize(v_i_2237_);
lean_dec(v_i_2237_);
v_res_2248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__0(v___x_2233_, v___x_2234_, v_as_2235_, v_sz_boxed_2246_, v_i_boxed_2247_, v_b_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_as_2235_);
lean_dec(v___x_2234_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(lean_object* v_00_u03b1_2249_, lean_object* v_ref_2250_, lean_object* v_msg_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_ref_2250_, v_msg_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2260_, lean_object* v_ref_2261_, lean_object* v_msg_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1(v_00_u03b1_2260_, v_ref_2261_, v_msg_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v_ref_2261_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_2271_, lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v_msg_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2281_, lean_object* v_msg_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2(v_00_u03b1_2281_, v_msg_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(lean_object* v_msgData_2291_, lean_object* v_macroStack_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___redArg(v_msgData_2291_, v_macroStack_2292_, v___y_2297_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_2301_, lean_object* v_macroStack_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2_spec__4(v_msgData_2301_, v_macroStack_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_2311_, lean_object* v_doc_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2320_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2328_; lean_object* v_env_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2320_ = lean_st_ref_get(v_a_2318_);
v_env_2335_ = lean_ctor_get(v___x_2320_, 0);
lean_inc_ref(v_env_2335_);
lean_dec(v___x_2320_);
v___x_2336_ = l_Lean_getMainVersoModuleDocs(v_env_2335_);
v___x_2337_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_2336_);
lean_dec_ref(v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
v___y_2328_ = v___x_2337_;
goto v___jp_2327_;
}
else
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2347_; 
v_val_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2347_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2347_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_add(v_val_2338_, v___x_2342_);
lean_dec(v_val_2338_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2343_);
v___x_2345_ = v___x_2340_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
v___y_2328_ = v___x_2345_;
goto v___jp_2327_;
}
}
}
v___jp_2321_:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_2324_, 0, v_range_2311_);
lean_closure_set(v___x_2324_, 1, v___y_2322_);
lean_closure_set(v___x_2324_, 2, v___y_2323_);
v___x_2325_ = 0;
v___x_2326_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_2324_, v___x_2325_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
return v___x_2326_;
}
v___jp_2327_:
{
lean_object* v___x_2329_; size_t v_sz_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = l_Lean_Syntax_getArgs(v_doc_2312_);
v_sz_2330_ = lean_array_size(v___x_2329_);
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_2330_, v___x_2331_, v___x_2329_);
if (lean_obj_tag(v___y_2328_) == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_unsigned_to_nat(0u);
v___y_2322_ = v___x_2332_;
v___y_2323_ = v___x_2333_;
goto v___jp_2321_;
}
else
{
lean_object* v_val_2334_; 
v_val_2334_ = lean_ctor_get(v___y_2328_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v___y_2328_, 1);
v___y_2322_ = v___x_2332_;
v___y_2323_ = v_val_2334_;
goto v___jp_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_2348_, lean_object* v_doc_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_versoModDocString(v_range_2348_, v_doc_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_doc_2349_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_2367_, lean_object* v_docComment_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_2377_ = l_Lean_versoDocStringOfText(v_declName_2367_, v___x_2376_, v_docComment_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_2378_, lean_object* v_docComment_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_versoDocStringFromString(v_declName_2378_, v_docComment_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_2388_, lean_object* v_declName_2389_, lean_object* v_env_2390_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = l_Lean_docStringExt;
v___x_2392_ = l_String_removeLeadingSpaces(v_docString_2388_);
v___x_2393_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2391_, v_env_2390_, v_declName_2389_, v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_2394_, lean_object* v_modifyEnv_2395_, lean_object* v_docString_2396_){
_start:
{
lean_object* v___f_2397_; lean_object* v___x_2398_; 
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2397_, 0, v_docString_2396_);
lean_closure_set(v___f_2397_, 1, v_declName_2394_);
v___x_2398_ = lean_apply_1(v_modifyEnv_2395_, v___f_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_docComment_2401_, lean_object* v_toBind_2402_, lean_object* v___f_2403_, lean_object* v_____r_2404_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = l_Lean_getDocStringText___redArg(v_inst_2399_, v_inst_2400_, v_docComment_2401_);
v___x_2406_ = lean_apply_4(v_toBind_2402_, lean_box(0), lean_box(0), v___x_2405_, v___f_2403_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_docComment_2412_, lean_object* v_toBind_2413_, lean_object* v___f_2414_, lean_object* v_____r_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = l_Lean_validateDocComment___redArg(v_inst_2407_, v_inst_2408_, v_inst_2409_, v_inst_2410_, v_inst_2411_, v_docComment_2412_);
v___x_2417_ = lean_apply_4(v_toBind_2413_, lean_box(0), lean_box(0), v___x_2416_, v___f_2414_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_docComment_2423_, lean_object* v_toBind_2424_, lean_object* v___f_2425_, lean_object* v_____r_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_2418_, v_inst_2419_, v_inst_2420_, v_inst_2421_, v_inst_2422_, v_docComment_2423_, v_toBind_2424_, v___f_2425_, v_____r_2426_);
lean_dec(v_docComment_2423_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_2428_, lean_object* v_____r_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_apply_1(v___f_2428_, v_____r_2429_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_2433_ = l_Lean_stringToMessageData(v___x_2432_);
return v___x_2433_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_2436_ = l_Lean_stringToMessageData(v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_2437_, lean_object* v_declName_2438_, uint8_t v___x_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_toBind_2442_, lean_object* v___f_2443_, lean_object* v_____do__lift_2444_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2444_, v_declName_2438_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_dec(v___f_2443_);
lean_dec(v_toBind_2442_);
lean_dec_ref(v_inst_2441_);
lean_dec_ref(v_inst_2440_);
lean_dec(v_declName_2438_);
goto v___jp_2445_;
}
else
{
lean_dec_ref_known(v___x_2448_, 1);
if (v___x_2439_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec(v___f_2437_);
v___x_2449_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2450_ = l_Lean_MessageData_ofConstName(v_declName_2438_, v___x_2439_);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l_Lean_throwError___redArg(v_inst_2440_, v_inst_2441_, v___x_2453_);
v___x_2455_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2454_, v___f_2443_);
return v___x_2455_;
}
else
{
lean_dec(v___f_2443_);
lean_dec(v_toBind_2442_);
lean_dec_ref(v_inst_2441_);
lean_dec_ref(v_inst_2440_);
lean_dec(v_declName_2438_);
goto v___jp_2445_;
}
}
v___jp_2445_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_box(0);
v___x_2447_ = lean_apply_1(v___f_2437_, v___x_2446_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_2456_, lean_object* v_declName_2457_, lean_object* v___x_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_toBind_2461_, lean_object* v___f_2462_, lean_object* v_____do__lift_2463_){
_start:
{
uint8_t v___x_247__boxed_2464_; lean_object* v_res_2465_; 
v___x_247__boxed_2464_ = lean_unbox(v___x_2458_);
v_res_2465_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_2456_, v_declName_2457_, v___x_247__boxed_2464_, v_inst_2459_, v_inst_2460_, v_toBind_2461_, v___f_2462_, v_____do__lift_2463_);
lean_dec_ref(v_____do__lift_2463_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_declName_2473_, lean_object* v_docComment_2474_){
_start:
{
lean_object* v_toApplicative_2475_; lean_object* v_toBind_2476_; lean_object* v_toPure_2477_; uint8_t v___x_2478_; 
v_toApplicative_2475_ = lean_ctor_get(v_inst_2466_, 0);
v_toBind_2476_ = lean_ctor_get(v_inst_2466_, 1);
lean_inc(v_toBind_2476_);
v_toPure_2477_ = lean_ctor_get(v_toApplicative_2475_, 1);
v___x_2478_ = l_Lean_Name_isAnonymous(v_declName_2473_);
if (v___x_2478_ == 0)
{
lean_object* v_getEnv_2479_; lean_object* v_modifyEnv_2480_; lean_object* v___f_2481_; lean_object* v___f_2482_; lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___x_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; 
v_getEnv_2479_ = lean_ctor_get(v_inst_2469_, 0);
lean_inc(v_getEnv_2479_);
v_modifyEnv_2480_ = lean_ctor_get(v_inst_2469_, 1);
lean_inc(v_modifyEnv_2480_);
lean_dec_ref(v_inst_2469_);
lean_inc(v_declName_2473_);
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2481_, 0, v_declName_2473_);
lean_closure_set(v___f_2481_, 1, v_modifyEnv_2480_);
lean_inc_n(v_toBind_2476_, 3);
lean_inc(v_docComment_2474_);
lean_inc_ref(v_inst_2470_);
lean_inc_ref_n(v_inst_2466_, 2);
v___f_2482_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_2482_, 0, v_inst_2466_);
lean_closure_set(v___f_2482_, 1, v_inst_2470_);
lean_closure_set(v___f_2482_, 2, v_docComment_2474_);
lean_closure_set(v___f_2482_, 3, v_toBind_2476_);
lean_closure_set(v___f_2482_, 4, v___f_2481_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2483_, 0, v_inst_2466_);
lean_closure_set(v___f_2483_, 1, v_inst_2467_);
lean_closure_set(v___f_2483_, 2, v_inst_2471_);
lean_closure_set(v___f_2483_, 3, v_inst_2472_);
lean_closure_set(v___f_2483_, 4, v_inst_2468_);
lean_closure_set(v___f_2483_, 5, v_docComment_2474_);
lean_closure_set(v___f_2483_, 6, v_toBind_2476_);
lean_closure_set(v___f_2483_, 7, v___f_2482_);
lean_inc_ref(v___f_2483_);
v___f_2484_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2484_, 0, v___f_2483_);
v___x_2485_ = lean_box(v___x_2478_);
v___f_2486_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_2486_, 0, v___f_2483_);
lean_closure_set(v___f_2486_, 1, v_declName_2473_);
lean_closure_set(v___f_2486_, 2, v___x_2485_);
lean_closure_set(v___f_2486_, 3, v_inst_2466_);
lean_closure_set(v___f_2486_, 4, v_inst_2470_);
lean_closure_set(v___f_2486_, 5, v_toBind_2476_);
lean_closure_set(v___f_2486_, 6, v___f_2484_);
v___x_2487_ = lean_apply_4(v_toBind_2476_, lean_box(0), lean_box(0), v_getEnv_2479_, v___f_2486_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
lean_inc(v_toPure_2477_);
lean_dec(v_toBind_2476_);
lean_dec(v_docComment_2474_);
lean_dec(v_declName_2473_);
lean_dec(v_inst_2472_);
lean_dec_ref(v_inst_2471_);
lean_dec_ref(v_inst_2470_);
lean_dec_ref(v_inst_2469_);
lean_dec(v_inst_2468_);
lean_dec(v_inst_2467_);
lean_dec_ref(v_inst_2466_);
v___x_2488_ = lean_box(0);
v___x_2489_ = lean_apply_2(v_toPure_2477_, lean_box(0), v___x_2488_);
return v___x_2489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_declName_2498_, lean_object* v_docComment_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_addMarkdownDocString___redArg(v_inst_2491_, v_inst_2492_, v_inst_2493_, v_inst_2494_, v_inst_2495_, v_inst_2496_, v_inst_2497_, v_declName_2498_, v_docComment_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_2501_, lean_object* v_x1_2502_, lean_object* v_x2_2503_){
_start:
{
lean_object* v_index_2504_; lean_object* v_sourceString_2505_; lean_object* v_imports_2506_; lean_object* v_currNamespace_2507_; lean_object* v_openDecls_2508_; lean_object* v_options_2509_; lean_object* v_check_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2523_; 
v_index_2504_ = lean_ctor_get(v_x2_2503_, 1);
v_sourceString_2505_ = lean_ctor_get(v_x2_2503_, 2);
v_imports_2506_ = lean_ctor_get(v_x2_2503_, 3);
v_currNamespace_2507_ = lean_ctor_get(v_x2_2503_, 4);
v_openDecls_2508_ = lean_ctor_get(v_x2_2503_, 5);
v_options_2509_ = lean_ctor_get(v_x2_2503_, 6);
v_check_2510_ = lean_ctor_get(v_x2_2503_, 7);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_x2_2503_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v_x2_2503_, 0);
lean_dec(v_unused_2524_);
v___x_2512_ = v_x2_2503_;
v_isShared_2513_ = v_isSharedCheck_2523_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_check_2510_);
lean_inc(v_options_2509_);
lean_inc(v_openDecls_2508_);
lean_inc(v_currNamespace_2507_);
lean_inc(v_imports_2506_);
lean_inc(v_sourceString_2505_);
lean_inc(v_index_2504_);
lean_dec(v_x2_2503_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2523_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v_toEnvExtension_2515_; lean_object* v_asyncMode_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2514_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2515_ = lean_ctor_get(v___x_2514_, 0);
v_asyncMode_2516_ = lean_ctor_get(v_toEnvExtension_2515_, 2);
v___x_2517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_declName_2501_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2517_);
v___x_2519_ = v___x_2512_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_index_2504_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_sourceString_2505_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_imports_2506_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_currNamespace_2507_);
lean_ctor_set(v_reuseFailAlloc_2522_, 5, v_openDecls_2508_);
lean_ctor_set(v_reuseFailAlloc_2522_, 6, v_options_2509_);
lean_ctor_set(v_reuseFailAlloc_2522_, 7, v_check_2510_);
v___x_2519_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_box(0);
v___x_2521_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2514_, v_x1_2502_, v___x_2519_, v_asyncMode_2516_, v___x_2520_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_2544_, lean_object* v_docs_2545_, lean_object* v_deferred_2546_, lean_object* v___f_2547_, lean_object* v_env_2548_){
_start:
{
lean_object* v___x_2549_; lean_object* v_env_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2549_ = l_Lean_versoDocStringExt;
v_env_2550_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2549_, v_env_2548_, v_declName_2544_, v_docs_2545_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_get_size(v_deferred_2546_);
v___x_2553_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2554_ = lean_nat_dec_lt(v___x_2551_, v___x_2552_);
if (v___x_2554_ == 0)
{
lean_dec_ref(v___f_2547_);
lean_dec_ref(v_deferred_2546_);
return v_env_2550_;
}
else
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_nat_dec_le(v___x_2552_, v___x_2552_);
if (v___x_2555_ == 0)
{
if (v___x_2554_ == 0)
{
lean_dec_ref(v___f_2547_);
lean_dec_ref(v_deferred_2546_);
return v_env_2550_;
}
else
{
size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = lean_usize_of_nat(v___x_2552_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2553_, v___f_2547_, v_deferred_2546_, v___x_2556_, v___x_2557_, v_env_2550_);
return v___x_2558_;
}
}
else
{
size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = lean_usize_of_nat(v___x_2552_);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2553_, v___f_2547_, v_deferred_2546_, v___x_2559_, v___x_2560_, v_env_2550_);
return v___x_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_2562_, lean_object* v___f_2563_, lean_object* v_____r_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_apply_1(v_modifyEnv_2562_, v___f_2563_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_2568_, lean_object* v_modifyEnv_2569_, lean_object* v___f_2570_, uint8_t v___x_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_toBind_2574_, lean_object* v___f_2575_, lean_object* v_____do__lift_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_2576_, v_declName_2568_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v___x_2578_; 
lean_dec(v___f_2575_);
lean_dec(v_toBind_2574_);
lean_dec_ref(v_inst_2573_);
lean_dec_ref(v_inst_2572_);
lean_dec(v_declName_2568_);
v___x_2578_ = lean_apply_1(v_modifyEnv_2569_, v___f_2570_);
return v___x_2578_;
}
else
{
lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2595_; 
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v___x_2577_, 0);
lean_dec(v_unused_2596_);
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2595_;
goto v_resetjp_2579_;
}
else
{
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2595_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
if (v___x_2571_ == 0)
{
lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec_ref(v___f_2570_);
lean_dec(v_modifyEnv_2569_);
v___x_2582_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2583_ = 1;
v___x_2584_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2568_, v___x_2583_);
v___x_2585_ = lean_string_append(v___x_2582_, v___x_2584_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2587_ = lean_string_append(v___x_2585_, v___x_2586_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 3);
lean_ctor_set(v___x_2580_, 0, v___x_2587_);
v___x_2589_ = v___x_2580_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = l_Lean_MessageData_ofFormat(v___x_2589_);
v___x_2591_ = l_Lean_throwError___redArg(v_inst_2572_, v_inst_2573_, v___x_2590_);
v___x_2592_ = lean_apply_4(v_toBind_2574_, lean_box(0), lean_box(0), v___x_2591_, v___f_2575_);
return v___x_2592_;
}
}
else
{
lean_object* v___x_2594_; 
lean_del_object(v___x_2580_);
lean_dec(v___f_2575_);
lean_dec(v_toBind_2574_);
lean_dec_ref(v_inst_2573_);
lean_dec_ref(v_inst_2572_);
lean_dec(v_declName_2568_);
v___x_2594_ = lean_apply_1(v_modifyEnv_2569_, v___f_2570_);
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_2597_, lean_object* v_modifyEnv_2598_, lean_object* v___f_2599_, lean_object* v___x_2600_, lean_object* v_inst_2601_, lean_object* v_inst_2602_, lean_object* v_toBind_2603_, lean_object* v___f_2604_, lean_object* v_____do__lift_2605_){
_start:
{
uint8_t v___x_374__boxed_2606_; lean_object* v_res_2607_; 
v___x_374__boxed_2606_ = lean_unbox(v___x_2600_);
v_res_2607_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_2597_, v_modifyEnv_2598_, v___f_2599_, v___x_374__boxed_2606_, v_inst_2601_, v_inst_2602_, v_toBind_2603_, v___f_2604_, v_____do__lift_2605_);
lean_dec_ref(v_____do__lift_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_declName_2611_, lean_object* v_docs_2612_, lean_object* v_deferred_2613_){
_start:
{
lean_object* v_toApplicative_2614_; lean_object* v_toBind_2615_; lean_object* v_toPure_2616_; uint8_t v___x_2617_; 
v_toApplicative_2614_ = lean_ctor_get(v_inst_2608_, 0);
v_toBind_2615_ = lean_ctor_get(v_inst_2608_, 1);
lean_inc(v_toBind_2615_);
v_toPure_2616_ = lean_ctor_get(v_toApplicative_2614_, 1);
v___x_2617_ = l_Lean_Name_isAnonymous(v_declName_2611_);
if (v___x_2617_ == 0)
{
lean_object* v_getEnv_2618_; lean_object* v_modifyEnv_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___x_2625_; 
v_getEnv_2618_ = lean_ctor_get(v_inst_2609_, 0);
lean_inc(v_getEnv_2618_);
v_modifyEnv_2619_ = lean_ctor_get(v_inst_2609_, 1);
lean_inc_n(v_modifyEnv_2619_, 2);
lean_dec_ref(v_inst_2609_);
lean_inc_n(v_declName_2611_, 2);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2620_, 0, v_declName_2611_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_2621_, 0, v_declName_2611_);
lean_closure_set(v___f_2621_, 1, v_docs_2612_);
lean_closure_set(v___f_2621_, 2, v_deferred_2613_);
lean_closure_set(v___f_2621_, 3, v___f_2620_);
lean_inc_ref(v___f_2621_);
v___f_2622_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2622_, 0, v_modifyEnv_2619_);
lean_closure_set(v___f_2622_, 1, v___f_2621_);
v___x_2623_ = lean_box(v___x_2617_);
lean_inc(v_toBind_2615_);
v___f_2624_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_2624_, 0, v_declName_2611_);
lean_closure_set(v___f_2624_, 1, v_modifyEnv_2619_);
lean_closure_set(v___f_2624_, 2, v___f_2621_);
lean_closure_set(v___f_2624_, 3, v___x_2623_);
lean_closure_set(v___f_2624_, 4, v_inst_2608_);
lean_closure_set(v___f_2624_, 5, v_inst_2610_);
lean_closure_set(v___f_2624_, 6, v_toBind_2615_);
lean_closure_set(v___f_2624_, 7, v___f_2622_);
v___x_2625_ = lean_apply_4(v_toBind_2615_, lean_box(0), lean_box(0), v_getEnv_2618_, v___f_2624_);
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_inc(v_toPure_2616_);
lean_dec(v_toBind_2615_);
lean_dec_ref(v_deferred_2613_);
lean_dec_ref(v_docs_2612_);
lean_dec(v_declName_2611_);
lean_dec_ref(v_inst_2610_);
lean_dec_ref(v_inst_2609_);
lean_dec_ref(v_inst_2608_);
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_apply_2(v_toPure_2616_, lean_box(0), v___x_2626_);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_2628_, lean_object* v_inst_2629_, lean_object* v_inst_2630_, lean_object* v_inst_2631_, lean_object* v_inst_2632_, lean_object* v_declName_2633_, lean_object* v_docs_2634_, lean_object* v_deferred_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_addVersoDocStringCore___redArg(v_inst_2629_, v_inst_2630_, v_inst_2632_, v_declName_2633_, v_docs_2634_, v_deferred_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_declName_2642_, lean_object* v_docs_2643_, lean_object* v_deferred_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Lean_addVersoDocStringCore(v_m_2637_, v_inst_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_declName_2642_, v_docs_2643_, v_deferred_2644_);
lean_dec(v_inst_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_2646_, lean_object* v_x1_2647_, lean_object* v_x2_2648_){
_start:
{
lean_object* v_index_2649_; lean_object* v_sourceString_2650_; lean_object* v_imports_2651_; lean_object* v_currNamespace_2652_; lean_object* v_openDecls_2653_; lean_object* v_options_2654_; lean_object* v_check_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2668_; 
v_index_2649_ = lean_ctor_get(v_x2_2648_, 1);
v_sourceString_2650_ = lean_ctor_get(v_x2_2648_, 2);
v_imports_2651_ = lean_ctor_get(v_x2_2648_, 3);
v_currNamespace_2652_ = lean_ctor_get(v_x2_2648_, 4);
v_openDecls_2653_ = lean_ctor_get(v_x2_2648_, 5);
v_options_2654_ = lean_ctor_get(v_x2_2648_, 6);
v_check_2655_ = lean_ctor_get(v_x2_2648_, 7);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_x2_2648_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; 
v_unused_2669_ = lean_ctor_get(v_x2_2648_, 0);
lean_dec(v_unused_2669_);
v___x_2657_ = v_x2_2648_;
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_check_2655_);
lean_inc(v_options_2654_);
lean_inc(v_openDecls_2653_);
lean_inc(v_currNamespace_2652_);
lean_inc(v_imports_2651_);
lean_inc(v_sourceString_2650_);
lean_inc(v_index_2649_);
lean_dec(v_x2_2648_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v_toEnvExtension_2660_; lean_object* v_asyncMode_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2659_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2660_ = lean_ctor_get(v___x_2659_, 0);
v_asyncMode_2661_ = lean_ctor_get(v_toEnvExtension_2660_, 2);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v_size_2646_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_index_2649_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_sourceString_2650_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v_imports_2651_);
lean_ctor_set(v_reuseFailAlloc_2667_, 4, v_currNamespace_2652_);
lean_ctor_set(v_reuseFailAlloc_2667_, 5, v_openDecls_2653_);
lean_ctor_set(v_reuseFailAlloc_2667_, 6, v_options_2654_);
lean_ctor_set(v_reuseFailAlloc_2667_, 7, v_check_2655_);
v___x_2664_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_box(0);
v___x_2666_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2659_, v_x1_2647_, v___x_2664_, v_asyncMode_2661_, v___x_2665_);
return v___x_2666_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_2672_ = l_Lean_stringToMessageData(v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_2673_, lean_object* v_inst_2674_, lean_object* v_inst_2675_, lean_object* v_deferred_2676_, lean_object* v_inst_2677_, lean_object* v___f_2678_, lean_object* v_____do__lift_2679_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_2679_, v_docs_2673_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref(v___f_2678_);
lean_dec_ref(v_inst_2677_);
lean_dec_ref(v_deferred_2676_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_2683_ = l_Lean_stringToMessageData(v_a_2681_);
v___x_2684_ = l_Lean_indentD(v___x_2683_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_throwError___redArg(v_inst_2674_, v_inst_2675_, v___x_2685_);
return v___x_2686_;
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
lean_dec_ref(v_inst_2675_);
lean_dec_ref(v_inst_2674_);
v_a_2687_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_array_get_size(v_deferred_2676_);
v___x_2690_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_2691_ = lean_nat_dec_lt(v___x_2688_, v___x_2689_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec_ref(v___f_2678_);
lean_dec_ref(v_deferred_2676_);
v___x_2692_ = l_Lean_setEnv___redArg(v_inst_2677_, v_a_2687_);
return v___x_2692_;
}
else
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_nat_dec_le(v___x_2689_, v___x_2689_);
if (v___x_2693_ == 0)
{
if (v___x_2691_ == 0)
{
lean_object* v___x_2694_; 
lean_dec_ref(v___f_2678_);
lean_dec_ref(v_deferred_2676_);
v___x_2694_ = l_Lean_setEnv___redArg(v_inst_2677_, v_a_2687_);
return v___x_2694_;
}
else
{
size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = ((size_t)0ULL);
v___x_2696_ = lean_usize_of_nat(v___x_2689_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2690_, v___f_2678_, v_deferred_2676_, v___x_2695_, v___x_2696_, v_a_2687_);
v___x_2698_ = l_Lean_setEnv___redArg(v_inst_2677_, v___x_2697_);
return v___x_2698_;
}
}
else
{
size_t v___x_2699_; size_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = lean_usize_of_nat(v___x_2689_);
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2690_, v___f_2678_, v_deferred_2676_, v___x_2699_, v___x_2700_, v_a_2687_);
v___x_2702_ = l_Lean_setEnv___redArg(v_inst_2677_, v___x_2701_);
return v___x_2702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_deferred_2706_, lean_object* v_inst_2707_, lean_object* v_toBind_2708_, lean_object* v_getEnv_2709_, lean_object* v_____do__lift_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v_size_2712_; lean_object* v___f_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; 
v___x_2711_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_2710_);
v_size_2712_ = lean_ctor_get(v___x_2711_, 2);
lean_inc(v_size_2712_);
lean_dec_ref(v___x_2711_);
v___f_2713_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2713_, 0, v_size_2712_);
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_2714_, 0, v_docs_2703_);
lean_closure_set(v___f_2714_, 1, v_inst_2704_);
lean_closure_set(v___f_2714_, 2, v_inst_2705_);
lean_closure_set(v___f_2714_, 3, v_deferred_2706_);
lean_closure_set(v___f_2714_, 4, v_inst_2707_);
lean_closure_set(v___f_2714_, 5, v___f_2713_);
v___x_2715_ = lean_apply_4(v_toBind_2708_, lean_box(0), lean_box(0), v_getEnv_2709_, v___f_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_toBind_2721_, lean_object* v_getEnv_2722_, lean_object* v___f_2723_, lean_object* v_____do__lift_2724_){
_start:
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = l_Lean_getMainModuleDoc(v_____do__lift_2724_);
v___x_2726_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2725_);
lean_dec_ref(v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec(v___f_2723_);
lean_dec(v_getEnv_2722_);
lean_dec(v_toBind_2721_);
v___x_2727_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2728_ = l_Lean_throwError___redArg(v_inst_2719_, v_inst_2720_, v___x_2727_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; 
lean_dec_ref(v_inst_2720_);
lean_dec_ref(v_inst_2719_);
v___x_2729_ = lean_apply_4(v_toBind_2721_, lean_box(0), lean_box(0), v_getEnv_2722_, v___f_2723_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_docs_2733_, lean_object* v_deferred_2734_){
_start:
{
lean_object* v_toBind_2735_; lean_object* v_getEnv_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; 
v_toBind_2735_ = lean_ctor_get(v_inst_2730_, 1);
lean_inc_n(v_toBind_2735_, 3);
v_getEnv_2736_ = lean_ctor_get(v_inst_2731_, 0);
lean_inc_n(v_getEnv_2736_, 3);
lean_inc_ref(v_inst_2732_);
lean_inc_ref(v_inst_2730_);
v___f_2737_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_2737_, 0, v_docs_2733_);
lean_closure_set(v___f_2737_, 1, v_inst_2730_);
lean_closure_set(v___f_2737_, 2, v_inst_2732_);
lean_closure_set(v___f_2737_, 3, v_deferred_2734_);
lean_closure_set(v___f_2737_, 4, v_inst_2731_);
lean_closure_set(v___f_2737_, 5, v_toBind_2735_);
lean_closure_set(v___f_2737_, 6, v_getEnv_2736_);
v___f_2738_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2738_, 0, v_inst_2730_);
lean_closure_set(v___f_2738_, 1, v_inst_2732_);
lean_closure_set(v___f_2738_, 2, v_toBind_2735_);
lean_closure_set(v___f_2738_, 3, v_getEnv_2736_);
lean_closure_set(v___f_2738_, 4, v___f_2737_);
v___x_2739_ = lean_apply_4(v_toBind_2735_, lean_box(0), lean_box(0), v_getEnv_2736_, v___f_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v_inst_2744_, lean_object* v_docs_2745_, lean_object* v_deferred_2746_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2741_, v_inst_2742_, v_inst_2744_, v_docs_2745_, v_deferred_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_inst_2752_, lean_object* v_docs_2753_, lean_object* v_deferred_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_addVersoModDocStringCore(v_m_2748_, v_inst_2749_, v_inst_2750_, v_inst_2751_, v_inst_2752_, v_docs_2753_, v_deferred_2754_);
lean_dec(v_inst_2751_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2756_, lean_object* v_as_2757_, size_t v_i_2758_, size_t v_stop_2759_, lean_object* v_b_2760_){
_start:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_usize_dec_eq(v_i_2758_, v_stop_2759_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v_index_2763_; lean_object* v_sourceString_2764_; lean_object* v_imports_2765_; lean_object* v_currNamespace_2766_; lean_object* v_openDecls_2767_; lean_object* v_options_2768_; lean_object* v_check_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2785_; 
v___x_2762_ = lean_array_uget(v_as_2757_, v_i_2758_);
v_index_2763_ = lean_ctor_get(v___x_2762_, 1);
v_sourceString_2764_ = lean_ctor_get(v___x_2762_, 2);
v_imports_2765_ = lean_ctor_get(v___x_2762_, 3);
v_currNamespace_2766_ = lean_ctor_get(v___x_2762_, 4);
v_openDecls_2767_ = lean_ctor_get(v___x_2762_, 5);
v_options_2768_ = lean_ctor_get(v___x_2762_, 6);
v_check_2769_ = lean_ctor_get(v___x_2762_, 7);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v___x_2762_, 0);
lean_dec(v_unused_2786_);
v___x_2771_ = v___x_2762_;
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_check_2769_);
lean_inc(v_options_2768_);
lean_inc(v_openDecls_2767_);
lean_inc(v_currNamespace_2766_);
lean_inc(v_imports_2765_);
lean_inc(v_sourceString_2764_);
lean_inc(v_index_2763_);
lean_dec(v___x_2762_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v_toEnvExtension_2774_; lean_object* v_asyncMode_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2773_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2774_ = lean_ctor_get(v___x_2773_, 0);
v_asyncMode_2775_ = lean_ctor_get(v_toEnvExtension_2774_, 2);
lean_inc(v_declName_2756_);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_declName_2756_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2776_);
v___x_2778_ = v___x_2771_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_index_2763_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_sourceString_2764_);
lean_ctor_set(v_reuseFailAlloc_2784_, 3, v_imports_2765_);
lean_ctor_set(v_reuseFailAlloc_2784_, 4, v_currNamespace_2766_);
lean_ctor_set(v_reuseFailAlloc_2784_, 5, v_openDecls_2767_);
lean_ctor_set(v_reuseFailAlloc_2784_, 6, v_options_2768_);
lean_ctor_set(v_reuseFailAlloc_2784_, 7, v_check_2769_);
v___x_2778_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; size_t v___x_2781_; size_t v___x_2782_; 
v___x_2779_ = lean_box(0);
v___x_2780_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2773_, v_b_2760_, v___x_2778_, v_asyncMode_2775_, v___x_2779_);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2758_, v___x_2781_);
v_i_2758_ = v___x_2782_;
v_b_2760_ = v___x_2780_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2756_);
return v_b_2760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2787_, lean_object* v_as_2788_, lean_object* v_i_2789_, lean_object* v_stop_2790_, lean_object* v_b_2791_){
_start:
{
size_t v_i_boxed_2792_; size_t v_stop_boxed_2793_; lean_object* v_res_2794_; 
v_i_boxed_2792_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_stop_boxed_2793_ = lean_unbox_usize(v_stop_2790_);
lean_dec(v_stop_2790_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2787_, v_as_2788_, v_i_boxed_2792_, v_stop_boxed_2793_, v_b_2791_);
lean_dec_ref(v_as_2788_);
return v_res_2794_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2795_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
return v___x_2799_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2801_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
lean_ctor_set(v___x_2801_, 3, v___x_2800_);
lean_ctor_set(v___x_2801_, 4, v___x_2800_);
lean_ctor_set(v___x_2801_, 5, v___x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2802_, lean_object* v_docs_2803_, lean_object* v_deferred_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2844_; lean_object* v___y_2845_; uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_Name_isAnonymous(v_declName_2802_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; lean_object* v_env_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_st_ref_get(v___y_2810_);
v_env_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc_ref(v_env_2865_);
lean_dec(v___x_2864_);
v___x_2866_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2865_, v_declName_2802_);
lean_dec_ref(v_env_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
v___y_2844_ = v___y_2808_;
v___y_2845_ = v___y_2810_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2881_; 
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2866_, 0);
lean_dec(v_unused_2882_);
v___x_2868_ = v___x_2866_;
v_isShared_2869_ = v_isSharedCheck_2881_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v___x_2866_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2881_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
if (v___x_2863_ == 0)
{
lean_object* v___x_2870_; uint8_t v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_dec_ref(v_docs_2803_);
v___x_2870_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2871_ = 1;
v___x_2872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2802_, v___x_2871_);
v___x_2873_ = lean_string_append(v___x_2870_, v___x_2872_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2875_ = lean_string_append(v___x_2873_, v___x_2874_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 3);
lean_ctor_set(v___x_2868_, 0, v___x_2875_);
v___x_2877_ = v___x_2868_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = l_Lean_MessageData_ofFormat(v___x_2877_);
v___x_2879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2878_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
return v___x_2879_;
}
}
else
{
lean_del_object(v___x_2868_);
v___y_2844_ = v___y_2808_;
v___y_2845_ = v___y_2810_;
goto v___jp_2843_;
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v_docs_2803_);
lean_dec(v_declName_2802_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
v___jp_2812_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v_mctx_2827_; lean_object* v_zetaDeltaFVarIds_2828_; lean_object* v_postponed_2829_; lean_object* v_diag_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2841_; 
v___x_2823_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2824_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2824_, 0, v___y_2822_);
lean_ctor_set(v___x_2824_, 1, v___y_2821_);
lean_ctor_set(v___x_2824_, 2, v___y_2817_);
lean_ctor_set(v___x_2824_, 3, v___y_2820_);
lean_ctor_set(v___x_2824_, 4, v___y_2818_);
lean_ctor_set(v___x_2824_, 5, v___x_2823_);
lean_ctor_set(v___x_2824_, 6, v___y_2819_);
lean_ctor_set(v___x_2824_, 7, v___y_2815_);
lean_ctor_set(v___x_2824_, 8, v___y_2814_);
v___x_2825_ = lean_st_ref_put(v___y_2813_, v___x_2824_);
v___x_2826_ = lean_st_ref_take(v___y_2816_);
v_mctx_2827_ = lean_ctor_get(v___x_2826_, 0);
v_zetaDeltaFVarIds_2828_ = lean_ctor_get(v___x_2826_, 2);
v_postponed_2829_ = lean_ctor_get(v___x_2826_, 3);
v_diag_2830_ = lean_ctor_get(v___x_2826_, 4);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2826_, 1);
lean_dec(v_unused_2842_);
v___x_2832_ = v___x_2826_;
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_diag_2830_);
lean_inc(v_postponed_2829_);
lean_inc(v_zetaDeltaFVarIds_2828_);
lean_inc(v_mctx_2827_);
lean_dec(v___x_2826_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2834_ = lean_box(0);
v___x_2835_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 1, v___x_2835_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_mctx_2827_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_zetaDeltaFVarIds_2828_);
lean_ctor_set(v_reuseFailAlloc_2840_, 3, v_postponed_2829_);
lean_ctor_set(v_reuseFailAlloc_2840_, 4, v_diag_2830_);
v___x_2837_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = lean_st_ref_put(v___y_2816_, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2834_);
return v___x_2839_;
}
}
}
v___jp_2843_:
{
lean_object* v___x_2846_; lean_object* v_env_2847_; lean_object* v_nextMacroScope_2848_; lean_object* v_ngen_2849_; lean_object* v_auxDeclNGen_2850_; lean_object* v_traceState_2851_; lean_object* v_messages_2852_; lean_object* v_infoState_2853_; lean_object* v_snapshotTasks_2854_; lean_object* v___x_2855_; lean_object* v_env_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2846_ = lean_st_ref_take(v___y_2845_);
v_env_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_ref(v_env_2847_);
v_nextMacroScope_2848_ = lean_ctor_get(v___x_2846_, 1);
lean_inc(v_nextMacroScope_2848_);
v_ngen_2849_ = lean_ctor_get(v___x_2846_, 2);
lean_inc_ref(v_ngen_2849_);
v_auxDeclNGen_2850_ = lean_ctor_get(v___x_2846_, 3);
lean_inc_ref(v_auxDeclNGen_2850_);
v_traceState_2851_ = lean_ctor_get(v___x_2846_, 4);
lean_inc_ref(v_traceState_2851_);
v_messages_2852_ = lean_ctor_get(v___x_2846_, 6);
lean_inc_ref(v_messages_2852_);
v_infoState_2853_ = lean_ctor_get(v___x_2846_, 7);
lean_inc_ref(v_infoState_2853_);
v_snapshotTasks_2854_ = lean_ctor_get(v___x_2846_, 8);
lean_inc_ref(v_snapshotTasks_2854_);
lean_dec(v___x_2846_);
v___x_2855_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2802_);
v_env_2856_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2855_, v_env_2847_, v_declName_2802_, v_docs_2803_);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_array_get_size(v_deferred_2804_);
v___x_2859_ = lean_nat_dec_lt(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_dec(v_declName_2802_);
v___y_2813_ = v___y_2845_;
v___y_2814_ = v_snapshotTasks_2854_;
v___y_2815_ = v_infoState_2853_;
v___y_2816_ = v___y_2844_;
v___y_2817_ = v_ngen_2849_;
v___y_2818_ = v_traceState_2851_;
v___y_2819_ = v_messages_2852_;
v___y_2820_ = v_auxDeclNGen_2850_;
v___y_2821_ = v_nextMacroScope_2848_;
v___y_2822_ = v_env_2856_;
goto v___jp_2812_;
}
else
{
size_t v___x_2860_; size_t v___x_2861_; lean_object* v___x_2862_; 
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = lean_usize_of_nat(v___x_2858_);
v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2802_, v_deferred_2804_, v___x_2860_, v___x_2861_, v_env_2856_);
v___y_2813_ = v___y_2845_;
v___y_2814_ = v_snapshotTasks_2854_;
v___y_2815_ = v_infoState_2853_;
v___y_2816_ = v___y_2844_;
v___y_2817_ = v_ngen_2849_;
v___y_2818_ = v_traceState_2851_;
v___y_2819_ = v_messages_2852_;
v___y_2820_ = v_auxDeclNGen_2850_;
v___y_2821_ = v_nextMacroScope_2848_;
v___y_2822_ = v___x_2862_;
goto v___jp_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2885_, lean_object* v_docs_2886_, lean_object* v_deferred_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2885_, v_docs_2886_, v_deferred_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_deferred_2887_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2896_, lean_object* v_binders_2897_, lean_object* v_docComment_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___x_2926_; lean_object* v_env_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_st_ref_get(v_a_2904_);
v_env_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref(v_env_2927_);
lean_dec(v___x_2926_);
v___x_2928_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2927_, v_declName_2896_);
lean_dec_ref(v_env_2927_);
if (lean_obj_tag(v___x_2928_) == 0)
{
v___y_2907_ = v_a_2899_;
v___y_2908_ = v_a_2900_;
v___y_2909_ = v_a_2901_;
v___y_2910_ = v_a_2902_;
v___y_2911_ = v_a_2903_;
v___y_2912_ = v_a_2904_;
goto v___jp_2906_;
}
else
{
lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_docComment_2898_);
lean_dec(v_binders_2897_);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2928_, 0);
lean_dec(v_unused_2944_);
v___x_2930_ = v___x_2928_;
v_isShared_2931_ = v_isSharedCheck_2943_;
goto v_resetjp_2929_;
}
else
{
lean_dec(v___x_2928_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2943_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2932_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2933_ = 1;
v___x_2934_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2896_, v___x_2933_);
v___x_2935_ = lean_string_append(v___x_2932_, v___x_2934_);
lean_dec_ref(v___x_2934_);
v___x_2936_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2937_ = lean_string_append(v___x_2935_, v___x_2936_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set_tag(v___x_2930_, 3);
lean_ctor_set(v___x_2930_, 0, v___x_2937_);
v___x_2939_ = v___x_2930_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = l_Lean_MessageData_ofFormat(v___x_2939_);
v___x_2941_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2940_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
return v___x_2941_;
}
}
}
v___jp_2906_:
{
lean_object* v___x_2913_; 
lean_inc(v_declName_2896_);
v___x_2913_ = l_Lean_versoDocString(v_declName_2896_, v_binders_2897_, v_docComment_2898_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_toVersoDocString_2915_; lean_object* v_deferredChecks_2916_; lean_object* v___x_2917_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v_toVersoDocString_2915_ = lean_ctor_get(v_a_2914_, 0);
lean_inc_ref(v_toVersoDocString_2915_);
v_deferredChecks_2916_ = lean_ctor_get(v_a_2914_, 1);
lean_inc_ref(v_deferredChecks_2916_);
lean_dec(v_a_2914_);
v___x_2917_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2896_, v_toVersoDocString_2915_, v_deferredChecks_2916_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec_ref(v_deferredChecks_2916_);
return v___x_2917_;
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_dec(v_declName_2896_);
v_a_2918_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2913_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2913_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2945_, lean_object* v_binders_2946_, lean_object* v_docComment_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_addVersoDocString(v_declName_2945_, v_binders_2946_, v_docComment_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2956_, lean_object* v_docComment_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___y_2966_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___x_2985_; lean_object* v_env_2986_; lean_object* v___x_2987_; 
v___x_2985_ = lean_st_ref_get(v_a_2963_);
v_env_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_env_2986_);
lean_dec(v___x_2985_);
v___x_2987_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2986_, v_declName_2956_);
lean_dec_ref(v_env_2986_);
if (lean_obj_tag(v___x_2987_) == 0)
{
v___y_2966_ = v_a_2958_;
v___y_2967_ = v_a_2959_;
v___y_2968_ = v_a_2960_;
v___y_2969_ = v_a_2961_;
v___y_2970_ = v_a_2962_;
v___y_2971_ = v_a_2963_;
goto v___jp_2965_;
}
else
{
lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v_docComment_2957_);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2987_, 0);
lean_dec(v_unused_3003_);
v___x_2989_ = v___x_2987_;
v_isShared_2990_ = v_isSharedCheck_3002_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v___x_2987_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3002_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2991_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2992_ = 1;
v___x_2993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2956_, v___x_2992_);
v___x_2994_ = lean_string_append(v___x_2991_, v___x_2993_);
lean_dec_ref(v___x_2993_);
v___x_2995_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 3);
lean_ctor_set(v___x_2989_, 0, v___x_2996_);
v___x_2998_ = v___x_2989_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = l_Lean_MessageData_ofFormat(v___x_2998_);
v___x_3000_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_2999_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_);
return v___x_3000_;
}
}
}
v___jp_2965_:
{
lean_object* v___x_2972_; 
lean_inc(v_declName_2956_);
v___x_2972_ = l_Lean_versoDocStringFromString(v_declName_2956_, v_docComment_2957_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v_toVersoDocString_2974_; lean_object* v_deferredChecks_2975_; lean_object* v___x_2976_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref_known(v___x_2972_, 1);
v_toVersoDocString_2974_ = lean_ctor_get(v_a_2973_, 0);
lean_inc_ref(v_toVersoDocString_2974_);
v_deferredChecks_2975_ = lean_ctor_get(v_a_2973_, 1);
lean_inc_ref(v_deferredChecks_2975_);
lean_dec(v_a_2973_);
v___x_2976_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2956_, v_toVersoDocString_2974_, v_deferredChecks_2975_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec_ref(v_deferredChecks_2975_);
return v___x_2976_;
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec(v_declName_2956_);
v_a_2977_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2972_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2972_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_3004_, lean_object* v_docComment_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_addVersoDocStringFromString(v_declName_3004_, v_docComment_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3014_, lean_object* v_msgData_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = 2;
v___x_3022_ = 0;
v___x_3023_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_3014_, v_msgData_3015_, v___x_3021_, v___x_3022_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3024_, lean_object* v_msgData_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3024_, v_msgData_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v_ref_3024_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_3032_, lean_object* v_str_3033_, lean_object* v_as_3034_, size_t v_sz_3035_, size_t v_i_3036_, lean_object* v_b_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_a_3046_; uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_lt(v_i_3036_, v_sz_3035_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v_b_3037_);
return v___x_3051_;
}
else
{
lean_object* v_a_3052_; lean_object* v_fst_3053_; lean_object* v_snd_3054_; lean_object* v_start_3055_; lean_object* v_stop_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3076_; 
v_a_3052_ = lean_array_uget_borrowed(v_as_3034_, v_i_3036_);
v_fst_3053_ = lean_ctor_get(v_a_3052_, 0);
lean_inc(v_fst_3053_);
v_snd_3054_ = lean_ctor_get(v_a_3052_, 1);
v_start_3055_ = lean_ctor_get(v_fst_3053_, 0);
v_stop_3056_ = lean_ctor_get(v_fst_3053_, 1);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_fst_3053_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3058_ = v_fst_3053_;
v_isShared_3059_ = v_isSharedCheck_3076_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_stop_3056_);
lean_inc(v_start_3055_);
lean_dec(v_fst_3053_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3076_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_box(0);
if (lean_obj_tag(v___y_3032_) == 1)
{
lean_object* v_val_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
v_val_3061_ = lean_ctor_get(v___y_3032_, 0);
v___x_3062_ = lean_nat_add(v_val_3061_, v_start_3055_);
v___x_3063_ = lean_nat_add(v_val_3061_, v_stop_3056_);
v___x_3064_ = 0;
v___x_3065_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3065_, 0, v___x_3062_);
lean_ctor_set(v___x_3065_, 1, v___x_3063_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*2, v___x_3064_);
v___x_3066_ = lean_string_utf8_extract(v_str_3033_, v_start_3055_, v_stop_3056_);
lean_dec(v_stop_3056_);
lean_dec(v_start_3055_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 2);
lean_ctor_set(v___x_3058_, 1, v___x_3066_);
lean_ctor_set(v___x_3058_, 0, v___x_3065_);
v___x_3068_ = v___x_3058_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_inc(v_snd_3054_);
v___x_3069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_snd_3054_);
v___x_3070_ = l_Lean_MessageData_ofFormat(v___x_3069_);
v___x_3071_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_3068_, v___x_3070_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec_ref(v___x_3068_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_dec_ref_known(v___x_3071_, 1);
v_a_3046_ = v___x_3060_;
goto v___jp_3045_;
}
else
{
return v___x_3071_;
}
}
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_del_object(v___x_3058_);
lean_dec(v_stop_3056_);
lean_dec(v_start_3055_);
lean_inc(v_snd_3054_);
v___x_3073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3073_, 0, v_snd_3054_);
v___x_3074_ = l_Lean_MessageData_ofFormat(v___x_3073_);
v___x_3075_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_3074_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_dec_ref_known(v___x_3075_, 1);
v_a_3046_ = v___x_3060_;
goto v___jp_3045_;
}
else
{
return v___x_3075_;
}
}
}
}
v___jp_3045_:
{
size_t v___x_3047_; size_t v___x_3048_; 
v___x_3047_ = ((size_t)1ULL);
v___x_3048_ = lean_usize_add(v_i_3036_, v___x_3047_);
v_i_3036_ = v___x_3048_;
v_b_3037_ = v_a_3046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_3077_, lean_object* v_str_3078_, lean_object* v_as_3079_, lean_object* v_sz_3080_, lean_object* v_i_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
size_t v_sz_boxed_3090_; size_t v_i_boxed_3091_; lean_object* v_res_3092_; 
v_sz_boxed_3090_ = lean_unbox_usize(v_sz_3080_);
lean_dec(v_sz_3080_);
v_i_boxed_3091_ = lean_unbox_usize(v_i_3081_);
lean_dec(v_i_3081_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3077_, v_str_3078_, v_as_3079_, v_sz_boxed_3090_, v_i_boxed_3091_, v_b_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_as_3079_);
lean_dec_ref(v_str_3078_);
lean_dec(v___y_3077_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v_str_3101_; lean_object* v___y_3103_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_str_3101_ = l_Lean_TSyntax_getDocString(v_docstring_3093_);
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = l_Lean_Syntax_getArg(v_docstring_3093_, v___x_3118_);
v___x_3120_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_3119_);
lean_dec(v___x_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_box(0);
v___y_3103_ = v___x_3121_;
goto v___jp_3102_;
}
else
{
lean_object* v_val_3122_; uint8_t v___x_3123_; lean_object* v___x_3124_; 
v_val_3122_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_val_3122_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3123_ = 0;
v___x_3124_ = l_Lean_SourceInfo_getPos_x3f(v_val_3122_, v___x_3123_);
lean_dec(v_val_3122_);
v___y_3103_ = v___x_3124_;
goto v___jp_3102_;
}
v___jp_3102_:
{
lean_object* v___x_3104_; lean_object* v_fst_3105_; lean_object* v___x_3106_; size_t v_sz_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref(v_str_3101_);
v___x_3104_ = l_Lean_rewriteManualLinksCore(v_str_3101_);
v_fst_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_fst_3105_);
lean_dec_ref(v___x_3104_);
v___x_3106_ = lean_box(0);
v_sz_3107_ = lean_array_size(v_fst_3105_);
v___x_3108_ = ((size_t)0ULL);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_3103_, v_str_3101_, v_fst_3105_, v_sz_3107_, v___x_3108_, v___x_3106_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
lean_dec(v_fst_3105_);
lean_dec_ref(v_str_3101_);
lean_dec(v___y_3103_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3109_, 0);
lean_dec(v_unused_3117_);
v___x_3111_ = v___x_3109_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v___x_3109_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3106_);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3106_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v_docstring_3125_);
return v_res_3133_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_3136_ = l_Lean_stringToMessageData(v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_val_3152_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(1u);
v___x_3160_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3159_);
switch(lean_obj_tag(v___x_3160_))
{
case 2:
{
lean_object* v_val_3161_; 
lean_dec(v_stx_3137_);
v_val_3161_ = lean_ctor_get(v___x_3160_, 1);
lean_inc_ref(v_val_3161_);
lean_dec_ref_known(v___x_3160_, 2);
v_val_3152_ = v_val_3161_;
goto v___jp_3151_;
}
case 1:
{
lean_object* v_kind_3162_; 
v_kind_3162_ = lean_ctor_get(v___x_3160_, 1);
lean_inc(v_kind_3162_);
if (lean_obj_tag(v_kind_3162_) == 1)
{
lean_object* v_pre_3163_; 
v_pre_3163_ = lean_ctor_get(v_kind_3162_, 0);
lean_inc(v_pre_3163_);
if (lean_obj_tag(v_pre_3163_) == 1)
{
lean_object* v_pre_3164_; 
v_pre_3164_ = lean_ctor_get(v_pre_3163_, 0);
lean_inc(v_pre_3164_);
if (lean_obj_tag(v_pre_3164_) == 1)
{
lean_object* v_pre_3165_; 
v_pre_3165_ = lean_ctor_get(v_pre_3164_, 0);
lean_inc(v_pre_3165_);
if (lean_obj_tag(v_pre_3165_) == 1)
{
lean_object* v_pre_3166_; 
v_pre_3166_ = lean_ctor_get(v_pre_3165_, 0);
if (lean_obj_tag(v_pre_3166_) == 0)
{
lean_object* v_str_3167_; lean_object* v_str_3168_; lean_object* v_str_3169_; lean_object* v_str_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_str_3167_ = lean_ctor_get(v_kind_3162_, 1);
lean_inc_ref(v_str_3167_);
lean_dec_ref_known(v_kind_3162_, 2);
v_str_3168_ = lean_ctor_get(v_pre_3163_, 1);
lean_inc_ref(v_str_3168_);
lean_dec_ref_known(v_pre_3163_, 2);
v_str_3169_ = lean_ctor_get(v_pre_3164_, 1);
lean_inc_ref(v_str_3169_);
lean_dec_ref_known(v_pre_3164_, 2);
v_str_3170_ = lean_ctor_get(v_pre_3165_, 1);
lean_inc_ref(v_str_3170_);
lean_dec_ref_known(v_pre_3165_, 2);
v___x_3171_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__0));
v___x_3172_ = lean_string_dec_eq(v_str_3170_, v___x_3171_);
lean_dec_ref(v_str_3170_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v_str_3169_);
lean_dec_ref(v_str_3168_);
lean_dec_ref(v_str_3167_);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__1));
v___x_3174_ = lean_string_dec_eq(v_str_3169_, v___x_3173_);
lean_dec_ref(v_str_3169_);
if (v___x_3174_ == 0)
{
lean_dec_ref(v_str_3168_);
lean_dec_ref(v_str_3167_);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3175_; uint8_t v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__2));
v___x_3176_ = lean_string_dec_eq(v_str_3168_, v___x_3175_);
lean_dec_ref(v_str_3168_);
if (v___x_3176_ == 0)
{
lean_dec_ref(v_str_3167_);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_parseVersoDocString___redArg___closed__5));
v___x_3178_ = lean_string_dec_eq(v_str_3167_, v___x_3177_);
lean_dec_ref(v_str_3167_);
if (v___x_3178_ == 0)
{
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_unsigned_to_nat(0u);
v___x_3180_ = l_Lean_Syntax_getArg(v___x_3160_, v___x_3179_);
lean_dec_ref_known(v___x_3160_, 3);
if (lean_obj_tag(v___x_3180_) == 2)
{
lean_object* v_val_3181_; 
lean_dec(v_stx_3137_);
v_val_3181_ = lean_ctor_get(v___x_3180_, 1);
lean_inc_ref(v_val_3181_);
lean_dec_ref_known(v___x_3180_, 2);
v_val_3152_ = v_val_3181_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v___x_3180_);
v___x_3182_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3137_);
v___x_3183_ = l_Lean_MessageData_ofSyntax(v_stx_3137_);
v___x_3184_ = l_Lean_indentD(v___x_3183_);
v___x_3185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3182_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3137_, v___x_3185_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v_stx_3137_);
return v___x_3186_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_3165_, 2);
lean_dec_ref_known(v_pre_3164_, 2);
lean_dec_ref_known(v_pre_3163_, 2);
lean_dec_ref_known(v_kind_3162_, 2);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
}
else
{
lean_dec_ref_known(v_pre_3164_, 2);
lean_dec(v_pre_3165_);
lean_dec_ref_known(v_pre_3163_, 2);
lean_dec_ref_known(v_kind_3162_, 2);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
}
else
{
lean_dec_ref_known(v_pre_3163_, 2);
lean_dec(v_pre_3164_);
lean_dec_ref_known(v_kind_3162_, 2);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
}
else
{
lean_dec_ref_known(v_kind_3162_, 2);
lean_dec(v_pre_3163_);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
}
else
{
lean_dec(v_kind_3162_);
lean_dec_ref_known(v___x_3160_, 3);
goto v___jp_3145_;
}
}
default: 
{
lean_dec(v___x_3160_);
goto v___jp_3145_;
}
}
v___jp_3145_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3146_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_3137_);
v___x_3147_ = l_Lean_MessageData_ofSyntax(v_stx_3137_);
v___x_3148_ = l_Lean_indentD(v___x_3147_);
v___x_3149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3146_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = l_Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1___redArg(v_stx_3137_, v___x_3149_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v_stx_3137_);
return v___x_3150_;
}
v___jp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = lean_string_utf8_byte_size(v_val_3152_);
v___x_3155_ = lean_unsigned_to_nat(2u);
v___x_3156_ = lean_nat_sub(v___x_3154_, v___x_3155_);
v___x_3157_ = lean_string_utf8_extract(v_val_3152_, v___x_3153_, v___x_3156_);
lean_dec(v___x_3156_);
lean_dec_ref(v_val_3152_);
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_3196_, lean_object* v_docComment_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___x_3268_; 
v___x_3268_ = l_Lean_Name_isAnonymous(v_declName_3196_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v_env_3270_; lean_object* v___x_3271_; 
v___x_3269_ = lean_st_ref_get(v___y_3203_);
v_env_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3269_);
v___x_3271_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3270_, v_declName_3196_);
lean_dec_ref(v_env_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
v___y_3206_ = v___y_3198_;
v___y_3207_ = v___y_3199_;
v___y_3208_ = v___y_3200_;
v___y_3209_ = v___y_3201_;
v___y_3210_ = v___y_3202_;
v___y_3211_ = v___y_3203_;
goto v___jp_3205_;
}
else
{
lean_dec_ref_known(v___x_3271_, 1);
if (v___x_3268_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_dec(v_docComment_3197_);
v___x_3272_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_3273_ = l_Lean_MessageData_ofConstName(v_declName_3196_, v___x_3268_);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_3276_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3277_;
}
else
{
v___y_3206_ = v___y_3198_;
v___y_3207_ = v___y_3199_;
v___y_3208_ = v___y_3200_;
v___y_3209_ = v___y_3201_;
v___y_3210_ = v___y_3202_;
v___y_3211_ = v___y_3203_;
goto v___jp_3205_;
}
}
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
lean_dec(v_docComment_3197_);
lean_dec(v_declName_3196_);
v___x_3278_ = lean_box(0);
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
v___jp_3205_:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_3197_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3212_, 1);
v___x_3213_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_3197_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3259_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3259_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3259_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v_env_3219_; lean_object* v_nextMacroScope_3220_; lean_object* v_ngen_3221_; lean_object* v_auxDeclNGen_3222_; lean_object* v_traceState_3223_; lean_object* v_messages_3224_; lean_object* v_infoState_3225_; lean_object* v_snapshotTasks_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3257_; 
v___x_3218_ = lean_st_ref_take(v___y_3211_);
v_env_3219_ = lean_ctor_get(v___x_3218_, 0);
v_nextMacroScope_3220_ = lean_ctor_get(v___x_3218_, 1);
v_ngen_3221_ = lean_ctor_get(v___x_3218_, 2);
v_auxDeclNGen_3222_ = lean_ctor_get(v___x_3218_, 3);
v_traceState_3223_ = lean_ctor_get(v___x_3218_, 4);
v_messages_3224_ = lean_ctor_get(v___x_3218_, 6);
v_infoState_3225_ = lean_ctor_get(v___x_3218_, 7);
v_snapshotTasks_3226_ = lean_ctor_get(v___x_3218_, 8);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3257_ == 0)
{
lean_object* v_unused_3258_; 
v_unused_3258_ = lean_ctor_get(v___x_3218_, 5);
lean_dec(v_unused_3258_);
v___x_3228_ = v___x_3218_;
v_isShared_3229_ = v_isSharedCheck_3257_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_snapshotTasks_3226_);
lean_inc(v_infoState_3225_);
lean_inc(v_messages_3224_);
lean_inc(v_traceState_3223_);
lean_inc(v_auxDeclNGen_3222_);
lean_inc(v_ngen_3221_);
lean_inc(v_nextMacroScope_3220_);
lean_inc(v_env_3219_);
lean_dec(v___x_3218_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3257_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3230_ = l_Lean_docStringExt;
v___x_3231_ = l_String_removeLeadingSpaces(v_a_3214_);
v___x_3232_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3230_, v_env_3219_, v_declName_3196_, v___x_3231_);
v___x_3233_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 5, v___x_3233_);
lean_ctor_set(v___x_3228_, 0, v___x_3232_);
v___x_3235_ = v___x_3228_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_nextMacroScope_3220_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_ngen_3221_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_auxDeclNGen_3222_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_traceState_3223_);
lean_ctor_set(v_reuseFailAlloc_3256_, 5, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3256_, 6, v_messages_3224_);
lean_ctor_set(v_reuseFailAlloc_3256_, 7, v_infoState_3225_);
lean_ctor_set(v_reuseFailAlloc_3256_, 8, v_snapshotTasks_3226_);
v___x_3235_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_mctx_3238_; lean_object* v_zetaDeltaFVarIds_3239_; lean_object* v_postponed_3240_; lean_object* v_diag_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3254_; 
v___x_3236_ = lean_st_ref_put(v___y_3211_, v___x_3235_);
v___x_3237_ = lean_st_ref_take(v___y_3209_);
v_mctx_3238_ = lean_ctor_get(v___x_3237_, 0);
v_zetaDeltaFVarIds_3239_ = lean_ctor_get(v___x_3237_, 2);
v_postponed_3240_ = lean_ctor_get(v___x_3237_, 3);
v_diag_3241_ = lean_ctor_get(v___x_3237_, 4);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v___x_3237_, 1);
lean_dec(v_unused_3255_);
v___x_3243_ = v___x_3237_;
v_isShared_3244_ = v_isSharedCheck_3254_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_diag_3241_);
lean_inc(v_postponed_3240_);
lean_inc(v_zetaDeltaFVarIds_3239_);
lean_inc(v_mctx_3238_);
lean_dec(v___x_3237_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3254_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 1, v___x_3246_);
v___x_3248_ = v___x_3243_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_mctx_3238_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3246_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_zetaDeltaFVarIds_3239_);
lean_ctor_set(v_reuseFailAlloc_3253_, 3, v_postponed_3240_);
lean_ctor_set(v_reuseFailAlloc_3253_, 4, v_diag_3241_);
v___x_3248_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = lean_st_ref_put(v___y_3209_, v___x_3248_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3245_);
v___x_3251_ = v___x_3216_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3245_);
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
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_declName_3196_);
v_a_3260_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3213_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3213_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_dec(v_docComment_3197_);
lean_dec(v_declName_3196_);
return v___x_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_3280_, lean_object* v_docComment_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3280_, v_docComment_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_3290_, lean_object* v_declName_3291_, lean_object* v_binders_3292_, lean_object* v_docComment_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
if (v_isVerso_3290_ == 0)
{
lean_object* v___x_3301_; 
lean_dec(v_binders_3292_);
v___x_3301_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_3291_, v_docComment_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
return v___x_3301_;
}
else
{
lean_object* v___x_3302_; 
v___x_3302_ = l_Lean_addVersoDocString(v_declName_3291_, v_binders_3292_, v_docComment_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_3303_, lean_object* v_declName_3304_, lean_object* v_binders_3305_, lean_object* v_docComment_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
uint8_t v_isVerso_boxed_3314_; lean_object* v_res_3315_; 
v_isVerso_boxed_3314_ = lean_unbox(v_isVerso_3303_);
v_res_3315_ = l_Lean_addDocStringOf(v_isVerso_boxed_3314_, v_declName_3304_, v_binders_3305_, v_docComment_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
lean_dec(v_a_3308_);
lean_dec_ref(v_a_3307_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_3316_, lean_object* v_msgData_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_3316_, v_msgData_3317_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_3326_, lean_object* v_msgData_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_3326_, v_msgData_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v_ref_3326_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_3336_, lean_object* v_t_3337_){
_start:
{
if (lean_obj_tag(v_t_3337_) == 0)
{
lean_object* v_k_3338_; lean_object* v_v_3339_; lean_object* v_l_3340_; lean_object* v_r_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3995_; 
v_k_3338_ = lean_ctor_get(v_t_3337_, 1);
v_v_3339_ = lean_ctor_get(v_t_3337_, 2);
v_l_3340_ = lean_ctor_get(v_t_3337_, 3);
v_r_3341_ = lean_ctor_get(v_t_3337_, 4);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_t_3337_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v_t_3337_, 0);
lean_dec(v_unused_3996_);
v___x_3343_ = v_t_3337_;
v_isShared_3344_ = v_isSharedCheck_3995_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_r_3341_);
lean_inc(v_l_3340_);
lean_inc(v_v_3339_);
lean_inc(v_k_3338_);
lean_dec(v_t_3337_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3995_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
uint8_t v___x_3345_; 
v___x_3345_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3336_, v_k_3338_);
switch(v___x_3345_)
{
case 0:
{
lean_object* v_impl_3346_; lean_object* v___x_3347_; 
v_impl_3346_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3336_, v_l_3340_);
v___x_3347_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3346_) == 0)
{
if (lean_obj_tag(v_r_3341_) == 0)
{
lean_object* v_size_3348_; lean_object* v_size_3349_; lean_object* v_k_3350_; lean_object* v_v_3351_; lean_object* v_l_3352_; lean_object* v_r_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; uint8_t v___x_3356_; 
v_size_3348_ = lean_ctor_get(v_impl_3346_, 0);
lean_inc(v_size_3348_);
v_size_3349_ = lean_ctor_get(v_r_3341_, 0);
v_k_3350_ = lean_ctor_get(v_r_3341_, 1);
v_v_3351_ = lean_ctor_get(v_r_3341_, 2);
v_l_3352_ = lean_ctor_get(v_r_3341_, 3);
lean_inc(v_l_3352_);
v_r_3353_ = lean_ctor_get(v_r_3341_, 4);
v___x_3354_ = lean_unsigned_to_nat(3u);
v___x_3355_ = lean_nat_mul(v___x_3354_, v_size_3348_);
v___x_3356_ = lean_nat_dec_lt(v___x_3355_, v_size_3349_);
lean_dec(v___x_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3360_; 
lean_dec(v_l_3352_);
v___x_3357_ = lean_nat_add(v___x_3347_, v_size_3348_);
lean_dec(v_size_3348_);
v___x_3358_ = lean_nat_add(v___x_3357_, v_size_3349_);
lean_dec(v___x_3357_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 3, v_impl_3346_);
lean_ctor_set(v___x_3343_, 0, v___x_3358_);
v___x_3360_ = v___x_3343_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_impl_3346_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_r_3341_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
else
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3425_; 
lean_inc(v_r_3353_);
lean_inc(v_v_3351_);
lean_inc(v_k_3350_);
lean_inc(v_size_3349_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3426_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_r_3341_, 2);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_r_3341_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3430_);
v___x_3363_ = v_r_3341_;
v_isShared_3364_ = v_isSharedCheck_3425_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v_r_3341_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3425_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v_size_3365_; lean_object* v_k_3366_; lean_object* v_v_3367_; lean_object* v_l_3368_; lean_object* v_r_3369_; lean_object* v_size_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v_size_3365_ = lean_ctor_get(v_l_3352_, 0);
v_k_3366_ = lean_ctor_get(v_l_3352_, 1);
v_v_3367_ = lean_ctor_get(v_l_3352_, 2);
v_l_3368_ = lean_ctor_get(v_l_3352_, 3);
v_r_3369_ = lean_ctor_get(v_l_3352_, 4);
v_size_3370_ = lean_ctor_get(v_r_3353_, 0);
v___x_3371_ = lean_unsigned_to_nat(2u);
v___x_3372_ = lean_nat_mul(v___x_3371_, v_size_3370_);
v___x_3373_ = lean_nat_dec_lt(v_size_3365_, v___x_3372_);
lean_dec(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3401_; 
lean_inc(v_r_3369_);
lean_inc(v_l_3368_);
lean_inc(v_v_3367_);
lean_inc(v_k_3366_);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_l_3352_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; lean_object* v_unused_3405_; lean_object* v_unused_3406_; 
v_unused_3402_ = lean_ctor_get(v_l_3352_, 4);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_l_3352_, 3);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_l_3352_, 2);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_l_3352_, 1);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v_l_3352_, 0);
lean_dec(v_unused_3406_);
v___x_3375_ = v_l_3352_;
v_isShared_3376_ = v_isSharedCheck_3401_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_l_3352_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3401_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3391_; 
v___x_3377_ = lean_nat_add(v___x_3347_, v_size_3348_);
lean_dec(v_size_3348_);
v___x_3378_ = lean_nat_add(v___x_3377_, v_size_3349_);
lean_dec(v_size_3349_);
if (lean_obj_tag(v_l_3368_) == 0)
{
lean_object* v_size_3399_; 
v_size_3399_ = lean_ctor_get(v_l_3368_, 0);
lean_inc(v_size_3399_);
v___y_3391_ = v_size_3399_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_unsigned_to_nat(0u);
v___y_3391_ = v___x_3400_;
goto v___jp_3390_;
}
v___jp_3379_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = lean_nat_add(v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 4, v_r_3353_);
lean_ctor_set(v___x_3375_, 3, v_r_3369_);
lean_ctor_set(v___x_3375_, 2, v_v_3351_);
lean_ctor_set(v___x_3375_, 1, v_k_3350_);
lean_ctor_set(v___x_3375_, 0, v___x_3383_);
v___x_3385_ = v___x_3375_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_k_3350_);
lean_ctor_set(v_reuseFailAlloc_3389_, 2, v_v_3351_);
lean_ctor_set(v_reuseFailAlloc_3389_, 3, v_r_3369_);
lean_ctor_set(v_reuseFailAlloc_3389_, 4, v_r_3353_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 4, v___x_3385_);
lean_ctor_set(v___x_3363_, 3, v___y_3380_);
lean_ctor_set(v___x_3363_, 2, v_v_3367_);
lean_ctor_set(v___x_3363_, 1, v_k_3366_);
lean_ctor_set(v___x_3363_, 0, v___x_3378_);
v___x_3387_ = v___x_3363_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_k_3366_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_v_3367_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v___y_3380_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
v___jp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_nat_add(v___x_3377_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec(v___x_3377_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_l_3368_);
lean_ctor_set(v___x_3343_, 3, v_impl_3346_);
lean_ctor_set(v___x_3343_, 0, v___x_3392_);
v___x_3394_ = v___x_3343_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3392_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3398_, 3, v_impl_3346_);
lean_ctor_set(v_reuseFailAlloc_3398_, 4, v_l_3368_);
v___x_3394_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_nat_add(v___x_3347_, v_size_3370_);
if (lean_obj_tag(v_r_3369_) == 0)
{
lean_object* v_size_3396_; 
v_size_3396_ = lean_ctor_get(v_r_3369_, 0);
lean_inc(v_size_3396_);
v___y_3380_ = v___x_3394_;
v___y_3381_ = v___x_3395_;
v___y_3382_ = v_size_3396_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_unsigned_to_nat(0u);
v___y_3380_ = v___x_3394_;
v___y_3381_ = v___x_3395_;
v___y_3382_ = v___x_3397_;
goto v___jp_3379_;
}
}
}
}
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3411_; 
lean_del_object(v___x_3343_);
v___x_3407_ = lean_nat_add(v___x_3347_, v_size_3348_);
lean_dec(v_size_3348_);
v___x_3408_ = lean_nat_add(v___x_3407_, v_size_3349_);
lean_dec(v_size_3349_);
v___x_3409_ = lean_nat_add(v___x_3407_, v_size_3365_);
lean_dec(v___x_3407_);
lean_inc_ref(v_impl_3346_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 4, v_l_3352_);
lean_ctor_set(v___x_3363_, 3, v_impl_3346_);
lean_ctor_set(v___x_3363_, 2, v_v_3339_);
lean_ctor_set(v___x_3363_, 1, v_k_3338_);
lean_ctor_set(v___x_3363_, 0, v___x_3409_);
v___x_3411_ = v___x_3363_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_impl_3346_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_l_3352_);
v___x_3411_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
v_isSharedCheck_3418_ = !lean_is_exclusive(v_impl_3346_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; lean_object* v_unused_3420_; lean_object* v_unused_3421_; lean_object* v_unused_3422_; lean_object* v_unused_3423_; 
v_unused_3419_ = lean_ctor_get(v_impl_3346_, 4);
lean_dec(v_unused_3419_);
v_unused_3420_ = lean_ctor_get(v_impl_3346_, 3);
lean_dec(v_unused_3420_);
v_unused_3421_ = lean_ctor_get(v_impl_3346_, 2);
lean_dec(v_unused_3421_);
v_unused_3422_ = lean_ctor_get(v_impl_3346_, 1);
lean_dec(v_unused_3422_);
v_unused_3423_ = lean_ctor_get(v_impl_3346_, 0);
lean_dec(v_unused_3423_);
v___x_3413_ = v_impl_3346_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_dec(v_impl_3346_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 4, v_r_3353_);
lean_ctor_set(v___x_3413_, 3, v___x_3411_);
lean_ctor_set(v___x_3413_, 2, v_v_3351_);
lean_ctor_set(v___x_3413_, 1, v_k_3350_);
lean_ctor_set(v___x_3413_, 0, v___x_3408_);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3408_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_3350_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_3351_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_r_3353_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v_size_3431_ = lean_ctor_get(v_impl_3346_, 0);
lean_inc(v_size_3431_);
v___x_3432_ = lean_nat_add(v___x_3347_, v_size_3431_);
lean_dec(v_size_3431_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 3, v_impl_3346_);
lean_ctor_set(v___x_3343_, 0, v___x_3432_);
v___x_3434_ = v___x_3343_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3435_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3435_, 3, v_impl_3346_);
lean_ctor_set(v_reuseFailAlloc_3435_, 4, v_r_3341_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
if (lean_obj_tag(v_r_3341_) == 0)
{
lean_object* v_l_3436_; 
v_l_3436_ = lean_ctor_get(v_r_3341_, 3);
lean_inc(v_l_3436_);
if (lean_obj_tag(v_l_3436_) == 0)
{
lean_object* v_r_3437_; 
v_r_3437_ = lean_ctor_get(v_r_3341_, 4);
lean_inc(v_r_3437_);
if (lean_obj_tag(v_r_3437_) == 0)
{
lean_object* v_size_3438_; lean_object* v_k_3439_; lean_object* v_v_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3453_; 
v_size_3438_ = lean_ctor_get(v_r_3341_, 0);
v_k_3439_ = lean_ctor_get(v_r_3341_, 1);
v_v_3440_ = lean_ctor_get(v_r_3341_, 2);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3453_ == 0)
{
lean_object* v_unused_3454_; lean_object* v_unused_3455_; 
v_unused_3454_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3454_);
v_unused_3455_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3455_);
v___x_3442_ = v_r_3341_;
v_isShared_3443_ = v_isSharedCheck_3453_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_v_3440_);
lean_inc(v_k_3439_);
lean_inc(v_size_3438_);
lean_dec(v_r_3341_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3453_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v_size_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v_size_3444_ = lean_ctor_get(v_l_3436_, 0);
v___x_3445_ = lean_nat_add(v___x_3347_, v_size_3438_);
lean_dec(v_size_3438_);
v___x_3446_ = lean_nat_add(v___x_3347_, v_size_3444_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 4, v_l_3436_);
lean_ctor_set(v___x_3442_, 3, v_impl_3346_);
lean_ctor_set(v___x_3442_, 2, v_v_3339_);
lean_ctor_set(v___x_3442_, 1, v_k_3338_);
lean_ctor_set(v___x_3442_, 0, v___x_3446_);
v___x_3448_ = v___x_3442_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3446_);
lean_ctor_set(v_reuseFailAlloc_3452_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3452_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3452_, 3, v_impl_3346_);
lean_ctor_set(v_reuseFailAlloc_3452_, 4, v_l_3436_);
v___x_3448_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3450_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_r_3437_);
lean_ctor_set(v___x_3343_, 3, v___x_3448_);
lean_ctor_set(v___x_3343_, 2, v_v_3440_);
lean_ctor_set(v___x_3343_, 1, v_k_3439_);
lean_ctor_set(v___x_3343_, 0, v___x_3445_);
v___x_3450_ = v___x_3343_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3439_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3440_);
lean_ctor_set(v_reuseFailAlloc_3451_, 3, v___x_3448_);
lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_r_3437_);
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
else
{
lean_object* v_k_3456_; lean_object* v_v_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3480_; 
v_k_3456_ = lean_ctor_get(v_r_3341_, 1);
v_v_3457_ = lean_ctor_get(v_r_3341_, 2);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3481_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3481_);
v_unused_3482_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3483_);
v___x_3459_ = v_r_3341_;
v_isShared_3460_ = v_isSharedCheck_3480_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_v_3457_);
lean_inc(v_k_3456_);
lean_dec(v_r_3341_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3480_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v_k_3461_; lean_object* v_v_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3476_; 
v_k_3461_ = lean_ctor_get(v_l_3436_, 1);
v_v_3462_ = lean_ctor_get(v_l_3436_, 2);
v_isSharedCheck_3476_ = !lean_is_exclusive(v_l_3436_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; lean_object* v_unused_3478_; lean_object* v_unused_3479_; 
v_unused_3477_ = lean_ctor_get(v_l_3436_, 4);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_l_3436_, 3);
lean_dec(v_unused_3478_);
v_unused_3479_ = lean_ctor_get(v_l_3436_, 0);
lean_dec(v_unused_3479_);
v___x_3464_ = v_l_3436_;
v_isShared_3465_ = v_isSharedCheck_3476_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_v_3462_);
lean_inc(v_k_3461_);
lean_dec(v_l_3436_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3476_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3466_ = lean_unsigned_to_nat(3u);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 4, v_r_3437_);
lean_ctor_set(v___x_3464_, 3, v_r_3437_);
lean_ctor_set(v___x_3464_, 2, v_v_3339_);
lean_ctor_set(v___x_3464_, 1, v_k_3338_);
lean_ctor_set(v___x_3464_, 0, v___x_3347_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3475_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3475_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3475_, 3, v_r_3437_);
lean_ctor_set(v_reuseFailAlloc_3475_, 4, v_r_3437_);
v___x_3468_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 3, v_r_3437_);
lean_ctor_set(v___x_3459_, 0, v___x_3347_);
v___x_3470_ = v___x_3459_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_k_3456_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_v_3457_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_r_3437_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_r_3437_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3470_);
lean_ctor_set(v___x_3343_, 3, v___x_3468_);
lean_ctor_set(v___x_3343_, 2, v_v_3462_);
lean_ctor_set(v___x_3343_, 1, v_k_3461_);
lean_ctor_set(v___x_3343_, 0, v___x_3466_);
v___x_3472_ = v___x_3343_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_3461_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_3462_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_3484_; 
v_r_3484_ = lean_ctor_get(v_r_3341_, 4);
lean_inc(v_r_3484_);
if (lean_obj_tag(v_r_3484_) == 0)
{
lean_object* v_k_3485_; lean_object* v_v_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3497_; 
v_k_3485_ = lean_ctor_get(v_r_3341_, 1);
v_v_3486_ = lean_ctor_get(v_r_3341_, 2);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; lean_object* v_unused_3499_; lean_object* v_unused_3500_; 
v_unused_3498_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3498_);
v_unused_3499_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3500_);
v___x_3488_ = v_r_3341_;
v_isShared_3489_ = v_isSharedCheck_3497_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_v_3486_);
lean_inc(v_k_3485_);
lean_dec(v_r_3341_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3497_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = lean_unsigned_to_nat(3u);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 4, v_l_3436_);
lean_ctor_set(v___x_3488_, 2, v_v_3339_);
lean_ctor_set(v___x_3488_, 1, v_k_3338_);
lean_ctor_set(v___x_3488_, 0, v___x_3347_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_l_3436_);
lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_l_3436_);
v___x_3492_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_r_3484_);
lean_ctor_set(v___x_3343_, 3, v___x_3492_);
lean_ctor_set(v___x_3343_, 2, v_v_3486_);
lean_ctor_set(v___x_3343_, 1, v_k_3485_);
lean_ctor_set(v___x_3343_, 0, v___x_3490_);
v___x_3494_ = v___x_3343_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3485_);
lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3486_);
lean_ctor_set(v_reuseFailAlloc_3495_, 3, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_r_3484_);
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
else
{
lean_object* v_size_3501_; lean_object* v_k_3502_; lean_object* v_v_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3514_; 
v_size_3501_ = lean_ctor_get(v_r_3341_, 0);
v_k_3502_ = lean_ctor_get(v_r_3341_, 1);
v_v_3503_ = lean_ctor_get(v_r_3341_, 2);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3514_ == 0)
{
lean_object* v_unused_3515_; lean_object* v_unused_3516_; 
v_unused_3515_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3515_);
v_unused_3516_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3516_);
v___x_3505_ = v_r_3341_;
v_isShared_3506_ = v_isSharedCheck_3514_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_v_3503_);
lean_inc(v_k_3502_);
lean_inc(v_size_3501_);
lean_dec(v_r_3341_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3514_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 3, v_r_3484_);
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_size_3501_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_k_3502_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v_v_3503_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v_r_3484_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v_r_3484_);
v___x_3508_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_unsigned_to_nat(2u);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3508_);
lean_ctor_set(v___x_3343_, 3, v_r_3484_);
lean_ctor_set(v___x_3343_, 0, v___x_3509_);
v___x_3511_ = v___x_3343_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3512_, 3, v_r_3484_);
lean_ctor_set(v_reuseFailAlloc_3512_, 4, v___x_3508_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
}
else
{
lean_object* v___x_3518_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 3, v_r_3341_);
lean_ctor_set(v___x_3343_, 0, v___x_3347_);
v___x_3518_ = v___x_3343_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3519_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3519_, 3, v_r_3341_);
lean_ctor_set(v_reuseFailAlloc_3519_, 4, v_r_3341_);
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
case 1:
{
lean_del_object(v___x_3343_);
lean_dec(v_v_3339_);
lean_dec(v_k_3338_);
if (lean_obj_tag(v_l_3340_) == 0)
{
if (lean_obj_tag(v_r_3341_) == 0)
{
lean_object* v_size_3520_; lean_object* v_k_3521_; lean_object* v_v_3522_; lean_object* v_l_3523_; lean_object* v_r_3524_; lean_object* v_size_3525_; lean_object* v_k_3526_; lean_object* v_v_3527_; lean_object* v_l_3528_; lean_object* v_r_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_size_3520_ = lean_ctor_get(v_l_3340_, 0);
v_k_3521_ = lean_ctor_get(v_l_3340_, 1);
v_v_3522_ = lean_ctor_get(v_l_3340_, 2);
v_l_3523_ = lean_ctor_get(v_l_3340_, 3);
v_r_3524_ = lean_ctor_get(v_l_3340_, 4);
lean_inc(v_r_3524_);
v_size_3525_ = lean_ctor_get(v_r_3341_, 0);
v_k_3526_ = lean_ctor_get(v_r_3341_, 1);
v_v_3527_ = lean_ctor_get(v_r_3341_, 2);
v_l_3528_ = lean_ctor_get(v_r_3341_, 3);
lean_inc(v_l_3528_);
v_r_3529_ = lean_ctor_get(v_r_3341_, 4);
v___x_3530_ = lean_unsigned_to_nat(1u);
v___x_3531_ = lean_nat_dec_lt(v_size_3520_, v_size_3525_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3667_; 
lean_inc(v_l_3523_);
lean_inc(v_v_3522_);
lean_inc(v_k_3521_);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; lean_object* v_unused_3669_; lean_object* v_unused_3670_; lean_object* v_unused_3671_; lean_object* v_unused_3672_; 
v_unused_3668_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3668_);
v_unused_3669_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3669_);
v_unused_3670_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3672_);
v___x_3533_ = v_l_3340_;
v_isShared_3534_ = v_isSharedCheck_3667_;
goto v_resetjp_3532_;
}
else
{
lean_dec(v_l_3340_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3667_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3535_; lean_object* v_tree_3536_; 
v___x_3535_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3521_, v_v_3522_, v_l_3523_, v_r_3524_);
v_tree_3536_ = lean_ctor_get(v___x_3535_, 2);
lean_inc(v_tree_3536_);
if (lean_obj_tag(v_tree_3536_) == 0)
{
lean_object* v_k_3537_; lean_object* v_v_3538_; lean_object* v_size_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v_k_3537_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_k_3537_);
v_v_3538_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_v_3538_);
lean_dec_ref(v___x_3535_);
v_size_3539_ = lean_ctor_get(v_tree_3536_, 0);
v___x_3540_ = lean_unsigned_to_nat(3u);
v___x_3541_ = lean_nat_mul(v___x_3540_, v_size_3539_);
v___x_3542_ = lean_nat_dec_lt(v___x_3541_, v_size_3525_);
lean_dec(v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3546_; 
lean_dec(v_l_3528_);
v___x_3543_ = lean_nat_add(v___x_3530_, v_size_3539_);
v___x_3544_ = lean_nat_add(v___x_3543_, v_size_3525_);
lean_dec(v___x_3543_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_r_3341_);
lean_ctor_set(v___x_3533_, 3, v_tree_3536_);
lean_ctor_set(v___x_3533_, 2, v_v_3538_);
lean_ctor_set(v___x_3533_, 1, v_k_3537_);
lean_ctor_set(v___x_3533_, 0, v___x_3544_);
v___x_3546_ = v___x_3533_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3547_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3547_, 3, v_tree_3536_);
lean_ctor_set(v_reuseFailAlloc_3547_, 4, v_r_3341_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
else
{
lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3602_; 
lean_inc(v_r_3529_);
lean_inc(v_v_3527_);
lean_inc(v_k_3526_);
lean_inc(v_size_3525_);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; lean_object* v_unused_3607_; 
v_unused_3603_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_r_3341_, 2);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_r_3341_, 1);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3607_);
v___x_3549_ = v_r_3341_;
v_isShared_3550_ = v_isSharedCheck_3602_;
goto v_resetjp_3548_;
}
else
{
lean_dec(v_r_3341_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3602_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v_size_3551_; lean_object* v_k_3552_; lean_object* v_v_3553_; lean_object* v_l_3554_; lean_object* v_r_3555_; lean_object* v_size_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v_size_3551_ = lean_ctor_get(v_l_3528_, 0);
v_k_3552_ = lean_ctor_get(v_l_3528_, 1);
v_v_3553_ = lean_ctor_get(v_l_3528_, 2);
v_l_3554_ = lean_ctor_get(v_l_3528_, 3);
v_r_3555_ = lean_ctor_get(v_l_3528_, 4);
v_size_3556_ = lean_ctor_get(v_r_3529_, 0);
v___x_3557_ = lean_unsigned_to_nat(2u);
v___x_3558_ = lean_nat_mul(v___x_3557_, v_size_3556_);
v___x_3559_ = lean_nat_dec_lt(v_size_3551_, v___x_3558_);
lean_dec(v___x_3558_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3587_; 
lean_inc(v_r_3555_);
lean_inc(v_l_3554_);
lean_inc(v_v_3553_);
lean_inc(v_k_3552_);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_l_3528_);
if (v_isSharedCheck_3587_ == 0)
{
lean_object* v_unused_3588_; lean_object* v_unused_3589_; lean_object* v_unused_3590_; lean_object* v_unused_3591_; lean_object* v_unused_3592_; 
v_unused_3588_ = lean_ctor_get(v_l_3528_, 4);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_l_3528_, 3);
lean_dec(v_unused_3589_);
v_unused_3590_ = lean_ctor_get(v_l_3528_, 2);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v_l_3528_, 1);
lean_dec(v_unused_3591_);
v_unused_3592_ = lean_ctor_get(v_l_3528_, 0);
lean_dec(v_unused_3592_);
v___x_3561_ = v_l_3528_;
v_isShared_3562_ = v_isSharedCheck_3587_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v_l_3528_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3587_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3577_; 
v___x_3563_ = lean_nat_add(v___x_3530_, v_size_3539_);
v___x_3564_ = lean_nat_add(v___x_3563_, v_size_3525_);
lean_dec(v_size_3525_);
if (lean_obj_tag(v_l_3554_) == 0)
{
lean_object* v_size_3585_; 
v_size_3585_ = lean_ctor_get(v_l_3554_, 0);
lean_inc(v_size_3585_);
v___y_3577_ = v_size_3585_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_unsigned_to_nat(0u);
v___y_3577_ = v___x_3586_;
goto v___jp_3576_;
}
v___jp_3565_:
{
lean_object* v___x_3569_; lean_object* v___x_3571_; 
v___x_3569_ = lean_nat_add(v___y_3567_, v___y_3568_);
lean_dec(v___y_3568_);
lean_dec(v___y_3567_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v_r_3529_);
lean_ctor_set(v___x_3561_, 3, v_r_3555_);
lean_ctor_set(v___x_3561_, 2, v_v_3527_);
lean_ctor_set(v___x_3561_, 1, v_k_3526_);
lean_ctor_set(v___x_3561_, 0, v___x_3569_);
v___x_3571_ = v___x_3561_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3569_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v_r_3555_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v_r_3529_);
v___x_3571_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
lean_object* v___x_3573_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 4, v___x_3571_);
lean_ctor_set(v___x_3549_, 3, v___y_3566_);
lean_ctor_set(v___x_3549_, 2, v_v_3553_);
lean_ctor_set(v___x_3549_, 1, v_k_3552_);
lean_ctor_set(v___x_3549_, 0, v___x_3564_);
v___x_3573_ = v___x_3549_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3564_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_k_3552_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_v_3553_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v___y_3566_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
v___jp_3576_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3578_ = lean_nat_add(v___x_3563_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec(v___x_3563_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_l_3554_);
lean_ctor_set(v___x_3533_, 3, v_tree_3536_);
lean_ctor_set(v___x_3533_, 2, v_v_3538_);
lean_ctor_set(v___x_3533_, 1, v_k_3537_);
lean_ctor_set(v___x_3533_, 0, v___x_3578_);
v___x_3580_ = v___x_3533_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_tree_3536_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_l_3554_);
v___x_3580_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_nat_add(v___x_3530_, v_size_3556_);
if (lean_obj_tag(v_r_3555_) == 0)
{
lean_object* v_size_3582_; 
v_size_3582_ = lean_ctor_get(v_r_3555_, 0);
lean_inc(v_size_3582_);
v___y_3566_ = v___x_3580_;
v___y_3567_ = v___x_3581_;
v___y_3568_ = v_size_3582_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3583_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___y_3566_ = v___x_3580_;
v___y_3567_ = v___x_3581_;
v___y_3568_ = v___x_3583_;
goto v___jp_3565_;
}
}
}
}
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3593_ = lean_nat_add(v___x_3530_, v_size_3539_);
v___x_3594_ = lean_nat_add(v___x_3593_, v_size_3525_);
lean_dec(v_size_3525_);
v___x_3595_ = lean_nat_add(v___x_3593_, v_size_3551_);
lean_dec(v___x_3593_);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 4, v_l_3528_);
lean_ctor_set(v___x_3549_, 3, v_tree_3536_);
lean_ctor_set(v___x_3549_, 2, v_v_3538_);
lean_ctor_set(v___x_3549_, 1, v_k_3537_);
lean_ctor_set(v___x_3549_, 0, v___x_3595_);
v___x_3597_ = v___x_3549_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_tree_3536_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_l_3528_);
v___x_3597_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3599_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_r_3529_);
lean_ctor_set(v___x_3533_, 3, v___x_3597_);
lean_ctor_set(v___x_3533_, 2, v_v_3527_);
lean_ctor_set(v___x_3533_, 1, v_k_3526_);
lean_ctor_set(v___x_3533_, 0, v___x_3594_);
v___x_3599_ = v___x_3533_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_r_3529_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
else
{
lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3661_; 
lean_inc(v_r_3529_);
lean_inc(v_v_3527_);
lean_inc(v_k_3526_);
lean_inc(v_size_3525_);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; lean_object* v_unused_3663_; lean_object* v_unused_3664_; lean_object* v_unused_3665_; lean_object* v_unused_3666_; 
v_unused_3662_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3662_);
v_unused_3663_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_r_3341_, 2);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_r_3341_, 1);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3666_);
v___x_3609_ = v_r_3341_;
v_isShared_3610_ = v_isSharedCheck_3661_;
goto v_resetjp_3608_;
}
else
{
lean_dec(v_r_3341_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3661_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
if (lean_obj_tag(v_l_3528_) == 0)
{
if (lean_obj_tag(v_r_3529_) == 0)
{
lean_object* v_k_3611_; lean_object* v_v_3612_; lean_object* v_size_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v_k_3611_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_k_3611_);
v_v_3612_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_v_3612_);
lean_dec_ref(v___x_3535_);
v_size_3613_ = lean_ctor_get(v_l_3528_, 0);
v___x_3614_ = lean_nat_add(v___x_3530_, v_size_3525_);
lean_dec(v_size_3525_);
v___x_3615_ = lean_nat_add(v___x_3530_, v_size_3613_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 4, v_l_3528_);
lean_ctor_set(v___x_3609_, 3, v_tree_3536_);
lean_ctor_set(v___x_3609_, 2, v_v_3612_);
lean_ctor_set(v___x_3609_, 1, v_k_3611_);
lean_ctor_set(v___x_3609_, 0, v___x_3615_);
v___x_3617_ = v___x_3609_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_k_3611_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_v_3612_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_tree_3536_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_l_3528_);
v___x_3617_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_r_3529_);
lean_ctor_set(v___x_3533_, 3, v___x_3617_);
lean_ctor_set(v___x_3533_, 2, v_v_3527_);
lean_ctor_set(v___x_3533_, 1, v_k_3526_);
lean_ctor_set(v___x_3533_, 0, v___x_3614_);
v___x_3619_ = v___x_3533_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3614_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_r_3529_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
else
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v_k_3624_; lean_object* v_v_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_size_3525_);
v_k_3622_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_k_3622_);
v_v_3623_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_v_3623_);
lean_dec_ref(v___x_3535_);
v_k_3624_ = lean_ctor_get(v_l_3528_, 1);
v_v_3625_ = lean_ctor_get(v_l_3528_, 2);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_l_3528_);
if (v_isSharedCheck_3639_ == 0)
{
lean_object* v_unused_3640_; lean_object* v_unused_3641_; lean_object* v_unused_3642_; 
v_unused_3640_ = lean_ctor_get(v_l_3528_, 4);
lean_dec(v_unused_3640_);
v_unused_3641_ = lean_ctor_get(v_l_3528_, 3);
lean_dec(v_unused_3641_);
v_unused_3642_ = lean_ctor_get(v_l_3528_, 0);
lean_dec(v_unused_3642_);
v___x_3627_ = v_l_3528_;
v_isShared_3628_ = v_isSharedCheck_3639_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_v_3625_);
lean_inc(v_k_3624_);
lean_dec(v_l_3528_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3639_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_unsigned_to_nat(3u);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 4, v_r_3529_);
lean_ctor_set(v___x_3627_, 3, v_r_3529_);
lean_ctor_set(v___x_3627_, 2, v_v_3623_);
lean_ctor_set(v___x_3627_, 1, v_k_3622_);
lean_ctor_set(v___x_3627_, 0, v___x_3530_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_k_3622_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_v_3623_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v_r_3529_);
v___x_3631_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 3, v_r_3529_);
lean_ctor_set(v___x_3609_, 0, v___x_3530_);
v___x_3633_ = v___x_3609_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_r_3529_);
v___x_3633_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v___x_3633_);
lean_ctor_set(v___x_3533_, 3, v___x_3631_);
lean_ctor_set(v___x_3533_, 2, v_v_3625_);
lean_ctor_set(v___x_3533_, 1, v_k_3624_);
lean_ctor_set(v___x_3533_, 0, v___x_3629_);
v___x_3635_ = v___x_3533_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3624_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3625_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3529_) == 0)
{
lean_object* v_k_3643_; lean_object* v_v_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_dec(v_size_3525_);
v_k_3643_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_k_3643_);
v_v_3644_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_v_3644_);
lean_dec_ref(v___x_3535_);
v___x_3645_ = lean_unsigned_to_nat(3u);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 4, v_l_3528_);
lean_ctor_set(v___x_3609_, 2, v_v_3644_);
lean_ctor_set(v___x_3609_, 1, v_k_3643_);
lean_ctor_set(v___x_3609_, 0, v___x_3530_);
v___x_3647_ = v___x_3609_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3643_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3644_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_l_3528_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_l_3528_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3649_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v_r_3529_);
lean_ctor_set(v___x_3533_, 3, v___x_3647_);
lean_ctor_set(v___x_3533_, 2, v_v_3527_);
lean_ctor_set(v___x_3533_, 1, v_k_3526_);
lean_ctor_set(v___x_3533_, 0, v___x_3645_);
v___x_3649_ = v___x_3533_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_r_3529_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v_k_3652_; lean_object* v_v_3653_; lean_object* v___x_3655_; 
v_k_3652_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_k_3652_);
v_v_3653_ = lean_ctor_get(v___x_3535_, 1);
lean_inc(v_v_3653_);
lean_dec_ref(v___x_3535_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 3, v_r_3529_);
v___x_3655_ = v___x_3609_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_size_3525_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3526_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3527_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_r_3529_);
v___x_3655_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3656_ = lean_unsigned_to_nat(2u);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 4, v___x_3655_);
lean_ctor_set(v___x_3533_, 3, v_r_3529_);
lean_ctor_set(v___x_3533_, 2, v_v_3653_);
lean_ctor_set(v___x_3533_, 1, v_k_3652_);
lean_ctor_set(v___x_3533_, 0, v___x_3656_);
v___x_3658_ = v___x_3533_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_k_3652_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_v_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_r_3529_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v___x_3655_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
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
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3825_; 
lean_inc(v_r_3529_);
lean_inc(v_v_3527_);
lean_inc(v_k_3526_);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_r_3341_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; lean_object* v_unused_3827_; lean_object* v_unused_3828_; lean_object* v_unused_3829_; lean_object* v_unused_3830_; 
v_unused_3826_ = lean_ctor_get(v_r_3341_, 4);
lean_dec(v_unused_3826_);
v_unused_3827_ = lean_ctor_get(v_r_3341_, 3);
lean_dec(v_unused_3827_);
v_unused_3828_ = lean_ctor_get(v_r_3341_, 2);
lean_dec(v_unused_3828_);
v_unused_3829_ = lean_ctor_get(v_r_3341_, 1);
lean_dec(v_unused_3829_);
v_unused_3830_ = lean_ctor_get(v_r_3341_, 0);
lean_dec(v_unused_3830_);
v___x_3674_ = v_r_3341_;
v_isShared_3675_ = v_isSharedCheck_3825_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v_r_3341_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3825_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v_tree_3677_; 
v___x_3676_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3526_, v_v_3527_, v_l_3528_, v_r_3529_);
v_tree_3677_ = lean_ctor_get(v___x_3676_, 2);
lean_inc(v_tree_3677_);
if (lean_obj_tag(v_tree_3677_) == 0)
{
lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v_size_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; 
v_k_3678_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_k_3678_);
v_v_3679_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_v_3679_);
lean_dec_ref(v___x_3676_);
v_size_3680_ = lean_ctor_get(v_tree_3677_, 0);
v___x_3681_ = lean_unsigned_to_nat(3u);
v___x_3682_ = lean_nat_mul(v___x_3681_, v_size_3680_);
v___x_3683_ = lean_nat_dec_lt(v___x_3682_, v_size_3520_);
lean_dec(v___x_3682_);
if (v___x_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec(v_r_3524_);
v___x_3684_ = lean_nat_add(v___x_3530_, v_size_3520_);
v___x_3685_ = lean_nat_add(v___x_3684_, v_size_3680_);
lean_dec(v___x_3684_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_tree_3677_);
lean_ctor_set(v___x_3674_, 3, v_l_3340_);
lean_ctor_set(v___x_3674_, 2, v_v_3679_);
lean_ctor_set(v___x_3674_, 1, v_k_3678_);
lean_ctor_set(v___x_3674_, 0, v___x_3685_);
v___x_3687_ = v___x_3674_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_tree_3677_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
else
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3754_; 
lean_inc(v_l_3523_);
lean_inc(v_v_3522_);
lean_inc(v_k_3521_);
lean_inc(v_size_3520_);
v_isSharedCheck_3754_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3755_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3759_);
v___x_3690_ = v_l_3340_;
v_isShared_3691_ = v_isSharedCheck_3754_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v_l_3340_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3754_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_size_3692_; lean_object* v_size_3693_; lean_object* v_k_3694_; lean_object* v_v_3695_; lean_object* v_l_3696_; lean_object* v_r_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; uint8_t v___x_3700_; 
v_size_3692_ = lean_ctor_get(v_l_3523_, 0);
v_size_3693_ = lean_ctor_get(v_r_3524_, 0);
v_k_3694_ = lean_ctor_get(v_r_3524_, 1);
v_v_3695_ = lean_ctor_get(v_r_3524_, 2);
v_l_3696_ = lean_ctor_get(v_r_3524_, 3);
v_r_3697_ = lean_ctor_get(v_r_3524_, 4);
v___x_3698_ = lean_unsigned_to_nat(2u);
v___x_3699_ = lean_nat_mul(v___x_3698_, v_size_3692_);
v___x_3700_ = lean_nat_dec_lt(v_size_3693_, v___x_3699_);
lean_dec(v___x_3699_);
if (v___x_3700_ == 0)
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3738_; 
lean_inc(v_r_3697_);
lean_inc(v_l_3696_);
lean_inc(v_v_3695_);
lean_inc(v_k_3694_);
lean_del_object(v___x_3690_);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_r_3524_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3739_ = lean_ctor_get(v_r_3524_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_r_3524_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_r_3524_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_r_3524_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_r_3524_, 0);
lean_dec(v_unused_3743_);
v___x_3702_ = v_r_3524_;
v_isShared_3703_ = v_isSharedCheck_3738_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_r_3524_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3738_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___x_3726_; lean_object* v___y_3728_; 
v___x_3704_ = lean_nat_add(v___x_3530_, v_size_3520_);
lean_dec(v_size_3520_);
v___x_3705_ = lean_nat_add(v___x_3704_, v_size_3680_);
lean_dec(v___x_3704_);
v___x_3726_ = lean_nat_add(v___x_3530_, v_size_3692_);
if (lean_obj_tag(v_l_3696_) == 0)
{
lean_object* v_size_3736_; 
v_size_3736_ = lean_ctor_get(v_l_3696_, 0);
lean_inc(v_size_3736_);
v___y_3728_ = v_size_3736_;
goto v___jp_3727_;
}
else
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_unsigned_to_nat(0u);
v___y_3728_ = v___x_3737_;
goto v___jp_3727_;
}
v___jp_3706_:
{
lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3710_ = lean_nat_add(v___y_3707_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec(v___y_3707_);
lean_inc_ref(v_tree_3677_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 4, v_tree_3677_);
lean_ctor_set(v___x_3702_, 3, v_r_3697_);
lean_ctor_set(v___x_3702_, 2, v_v_3679_);
lean_ctor_set(v___x_3702_, 1, v_k_3678_);
lean_ctor_set(v___x_3702_, 0, v___x_3710_);
v___x_3712_ = v___x_3702_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_r_3697_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_tree_3677_);
v___x_3712_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
v_isSharedCheck_3719_ = !lean_is_exclusive(v_tree_3677_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; lean_object* v_unused_3721_; lean_object* v_unused_3722_; lean_object* v_unused_3723_; lean_object* v_unused_3724_; 
v_unused_3720_ = lean_ctor_get(v_tree_3677_, 4);
lean_dec(v_unused_3720_);
v_unused_3721_ = lean_ctor_get(v_tree_3677_, 3);
lean_dec(v_unused_3721_);
v_unused_3722_ = lean_ctor_get(v_tree_3677_, 2);
lean_dec(v_unused_3722_);
v_unused_3723_ = lean_ctor_get(v_tree_3677_, 1);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_tree_3677_, 0);
lean_dec(v_unused_3724_);
v___x_3714_ = v_tree_3677_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v_tree_3677_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 4, v___x_3712_);
lean_ctor_set(v___x_3714_, 3, v___y_3708_);
lean_ctor_set(v___x_3714_, 2, v_v_3695_);
lean_ctor_set(v___x_3714_, 1, v_k_3694_);
lean_ctor_set(v___x_3714_, 0, v___x_3705_);
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_k_3694_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_v_3695_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v___y_3708_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v___x_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
v___jp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3729_ = lean_nat_add(v___x_3726_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec(v___x_3726_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_l_3696_);
lean_ctor_set(v___x_3674_, 3, v_l_3523_);
lean_ctor_set(v___x_3674_, 2, v_v_3522_);
lean_ctor_set(v___x_3674_, 1, v_k_3521_);
lean_ctor_set(v___x_3674_, 0, v___x_3729_);
v___x_3731_ = v___x_3674_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3735_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3735_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3735_, 4, v_l_3696_);
v___x_3731_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_nat_add(v___x_3530_, v_size_3680_);
if (lean_obj_tag(v_r_3697_) == 0)
{
lean_object* v_size_3733_; 
v_size_3733_ = lean_ctor_get(v_r_3697_, 0);
lean_inc(v_size_3733_);
v___y_3707_ = v___x_3732_;
v___y_3708_ = v___x_3731_;
v___y_3709_ = v_size_3733_;
goto v___jp_3706_;
}
else
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_unsigned_to_nat(0u);
v___y_3707_ = v___x_3732_;
v___y_3708_ = v___x_3731_;
v___y_3709_ = v___x_3734_;
goto v___jp_3706_;
}
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v___x_3744_ = lean_nat_add(v___x_3530_, v_size_3520_);
lean_dec(v_size_3520_);
v___x_3745_ = lean_nat_add(v___x_3744_, v_size_3680_);
lean_dec(v___x_3744_);
v___x_3746_ = lean_nat_add(v___x_3530_, v_size_3680_);
v___x_3747_ = lean_nat_add(v___x_3746_, v_size_3693_);
lean_dec(v___x_3746_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_tree_3677_);
lean_ctor_set(v___x_3674_, 3, v_r_3524_);
lean_ctor_set(v___x_3674_, 2, v_v_3679_);
lean_ctor_set(v___x_3674_, 1, v_k_3678_);
lean_ctor_set(v___x_3674_, 0, v___x_3747_);
v___x_3749_ = v___x_3674_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_r_3524_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v_tree_3677_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 4, v___x_3749_);
lean_ctor_set(v___x_3690_, 0, v___x_3745_);
v___x_3751_ = v___x_3690_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3752_, 4, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3523_) == 0)
{
lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3783_; 
lean_inc_ref(v_l_3523_);
lean_inc(v_v_3522_);
lean_inc(v_k_3521_);
lean_inc(v_size_3520_);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3783_ == 0)
{
lean_object* v_unused_3784_; lean_object* v_unused_3785_; lean_object* v_unused_3786_; lean_object* v_unused_3787_; lean_object* v_unused_3788_; 
v_unused_3784_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3785_);
v_unused_3786_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3786_);
v_unused_3787_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3788_);
v___x_3761_ = v_l_3340_;
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
else
{
lean_dec(v_l_3340_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
if (lean_obj_tag(v_r_3524_) == 0)
{
lean_object* v_k_3763_; lean_object* v_v_3764_; lean_object* v_size_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3769_; 
v_k_3763_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_k_3763_);
v_v_3764_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_v_3764_);
lean_dec_ref(v___x_3676_);
v_size_3765_ = lean_ctor_get(v_r_3524_, 0);
v___x_3766_ = lean_nat_add(v___x_3530_, v_size_3520_);
lean_dec(v_size_3520_);
v___x_3767_ = lean_nat_add(v___x_3530_, v_size_3765_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_tree_3677_);
lean_ctor_set(v___x_3674_, 3, v_r_3524_);
lean_ctor_set(v___x_3674_, 2, v_v_3764_);
lean_ctor_set(v___x_3674_, 1, v_k_3763_);
lean_ctor_set(v___x_3674_, 0, v___x_3767_);
v___x_3769_ = v___x_3674_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_k_3763_);
lean_ctor_set(v_reuseFailAlloc_3773_, 2, v_v_3764_);
lean_ctor_set(v_reuseFailAlloc_3773_, 3, v_r_3524_);
lean_ctor_set(v_reuseFailAlloc_3773_, 4, v_tree_3677_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 4, v___x_3769_);
lean_ctor_set(v___x_3761_, 0, v___x_3766_);
v___x_3771_ = v___x_3761_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
else
{
lean_object* v_k_3774_; lean_object* v_v_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
lean_dec(v_size_3520_);
v_k_3774_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_k_3774_);
v_v_3775_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_v_3775_);
lean_dec_ref(v___x_3676_);
v___x_3776_ = lean_unsigned_to_nat(3u);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_r_3524_);
lean_ctor_set(v___x_3674_, 3, v_r_3524_);
lean_ctor_set(v___x_3674_, 2, v_v_3775_);
lean_ctor_set(v___x_3674_, 1, v_k_3774_);
lean_ctor_set(v___x_3674_, 0, v___x_3530_);
v___x_3778_ = v___x_3674_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_k_3774_);
lean_ctor_set(v_reuseFailAlloc_3782_, 2, v_v_3775_);
lean_ctor_set(v_reuseFailAlloc_3782_, 3, v_r_3524_);
lean_ctor_set(v_reuseFailAlloc_3782_, 4, v_r_3524_);
v___x_3778_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 4, v___x_3778_);
lean_ctor_set(v___x_3761_, 0, v___x_3776_);
v___x_3780_ = v___x_3761_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3776_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3524_) == 0)
{
lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3813_; 
lean_inc(v_l_3523_);
lean_inc(v_v_3522_);
lean_inc(v_k_3521_);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; 
v_unused_3814_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3818_);
v___x_3790_ = v_l_3340_;
v_isShared_3791_ = v_isSharedCheck_3813_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v_l_3340_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3813_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v_k_3792_; lean_object* v_v_3793_; lean_object* v_k_3794_; lean_object* v_v_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3809_; 
v_k_3792_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_k_3792_);
v_v_3793_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_v_3793_);
lean_dec_ref(v___x_3676_);
v_k_3794_ = lean_ctor_get(v_r_3524_, 1);
v_v_3795_ = lean_ctor_get(v_r_3524_, 2);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_r_3524_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; 
v_unused_3810_ = lean_ctor_get(v_r_3524_, 4);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_r_3524_, 3);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_r_3524_, 0);
lean_dec(v_unused_3812_);
v___x_3797_ = v_r_3524_;
v_isShared_3798_ = v_isSharedCheck_3809_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_v_3795_);
lean_inc(v_k_3794_);
lean_dec(v_r_3524_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3809_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3799_ = lean_unsigned_to_nat(3u);
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 4, v_l_3523_);
lean_ctor_set(v___x_3797_, 3, v_l_3523_);
lean_ctor_set(v___x_3797_, 2, v_v_3522_);
lean_ctor_set(v___x_3797_, 1, v_k_3521_);
lean_ctor_set(v___x_3797_, 0, v___x_3530_);
v___x_3801_ = v___x_3797_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_k_3521_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_v_3522_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_l_3523_);
v___x_3801_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_l_3523_);
lean_ctor_set(v___x_3674_, 3, v_l_3523_);
lean_ctor_set(v___x_3674_, 2, v_v_3793_);
lean_ctor_set(v___x_3674_, 1, v_k_3792_);
lean_ctor_set(v___x_3674_, 0, v___x_3530_);
v___x_3803_ = v___x_3674_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_k_3792_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v_v_3793_);
lean_ctor_set(v_reuseFailAlloc_3807_, 3, v_l_3523_);
lean_ctor_set(v_reuseFailAlloc_3807_, 4, v_l_3523_);
v___x_3803_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3805_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 4, v___x_3803_);
lean_ctor_set(v___x_3790_, 3, v___x_3801_);
lean_ctor_set(v___x_3790_, 2, v_v_3795_);
lean_ctor_set(v___x_3790_, 1, v_k_3794_);
lean_ctor_set(v___x_3790_, 0, v___x_3799_);
v___x_3805_ = v___x_3790_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_k_3794_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_v_3795_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v___x_3801_);
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
}
else
{
lean_object* v_k_3819_; lean_object* v_v_3820_; lean_object* v___x_3821_; lean_object* v___x_3823_; 
v_k_3819_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_k_3819_);
v_v_3820_ = lean_ctor_get(v___x_3676_, 1);
lean_inc(v_v_3820_);
lean_dec_ref(v___x_3676_);
v___x_3821_ = lean_unsigned_to_nat(2u);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_r_3524_);
lean_ctor_set(v___x_3674_, 3, v_l_3340_);
lean_ctor_set(v___x_3674_, 2, v_v_3820_);
lean_ctor_set(v___x_3674_, 1, v_k_3819_);
lean_ctor_set(v___x_3674_, 0, v___x_3821_);
v___x_3823_ = v___x_3674_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_k_3819_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_v_3820_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v_r_3524_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
}
}
else
{
return v_l_3340_;
}
}
else
{
return v_r_3341_;
}
}
default: 
{
lean_object* v_impl_3831_; lean_object* v___x_3832_; 
v_impl_3831_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3336_, v_r_3341_);
v___x_3832_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3831_) == 0)
{
if (lean_obj_tag(v_l_3340_) == 0)
{
lean_object* v_size_3833_; lean_object* v_size_3834_; lean_object* v_k_3835_; lean_object* v_v_3836_; lean_object* v_l_3837_; lean_object* v_r_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_size_3833_ = lean_ctor_get(v_impl_3831_, 0);
lean_inc(v_size_3833_);
v_size_3834_ = lean_ctor_get(v_l_3340_, 0);
v_k_3835_ = lean_ctor_get(v_l_3340_, 1);
v_v_3836_ = lean_ctor_get(v_l_3340_, 2);
v_l_3837_ = lean_ctor_get(v_l_3340_, 3);
v_r_3838_ = lean_ctor_get(v_l_3340_, 4);
lean_inc(v_r_3838_);
v___x_3839_ = lean_unsigned_to_nat(3u);
v___x_3840_ = lean_nat_mul(v___x_3839_, v_size_3833_);
v___x_3841_ = lean_nat_dec_lt(v___x_3840_, v_size_3834_);
lean_dec(v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec(v_r_3838_);
v___x_3842_ = lean_nat_add(v___x_3832_, v_size_3834_);
v___x_3843_ = lean_nat_add(v___x_3842_, v_size_3833_);
lean_dec(v_size_3833_);
lean_dec(v___x_3842_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_impl_3831_);
lean_ctor_set(v___x_3343_, 0, v___x_3843_);
v___x_3845_ = v___x_3343_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3846_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3846_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3846_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3846_, 4, v_impl_3831_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
else
{
lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3912_; 
lean_inc(v_l_3837_);
lean_inc(v_v_3836_);
lean_inc(v_k_3835_);
lean_inc(v_size_3834_);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; 
v_unused_3913_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3913_);
v_unused_3914_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_l_3340_, 2);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3340_, 1);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3917_);
v___x_3848_ = v_l_3340_;
v_isShared_3849_ = v_isSharedCheck_3912_;
goto v_resetjp_3847_;
}
else
{
lean_dec(v_l_3340_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3912_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_size_3850_; lean_object* v_size_3851_; lean_object* v_k_3852_; lean_object* v_v_3853_; lean_object* v_l_3854_; lean_object* v_r_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_size_3850_ = lean_ctor_get(v_l_3837_, 0);
v_size_3851_ = lean_ctor_get(v_r_3838_, 0);
v_k_3852_ = lean_ctor_get(v_r_3838_, 1);
v_v_3853_ = lean_ctor_get(v_r_3838_, 2);
v_l_3854_ = lean_ctor_get(v_r_3838_, 3);
v_r_3855_ = lean_ctor_get(v_r_3838_, 4);
v___x_3856_ = lean_unsigned_to_nat(2u);
v___x_3857_ = lean_nat_mul(v___x_3856_, v_size_3850_);
v___x_3858_ = lean_nat_dec_lt(v_size_3851_, v___x_3857_);
lean_dec(v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3887_; 
lean_inc(v_r_3855_);
lean_inc(v_l_3854_);
lean_inc(v_v_3853_);
lean_inc(v_k_3852_);
v_isSharedCheck_3887_ = !lean_is_exclusive(v_r_3838_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3888_ = lean_ctor_get(v_r_3838_, 4);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_r_3838_, 3);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_r_3838_, 2);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_r_3838_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_r_3838_, 0);
lean_dec(v_unused_3892_);
v___x_3860_ = v_r_3838_;
v_isShared_3861_ = v_isSharedCheck_3887_;
goto v_resetjp_3859_;
}
else
{
lean_dec(v_r_3838_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3887_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___x_3875_; lean_object* v___y_3877_; 
v___x_3862_ = lean_nat_add(v___x_3832_, v_size_3834_);
lean_dec(v_size_3834_);
v___x_3863_ = lean_nat_add(v___x_3862_, v_size_3833_);
lean_dec(v___x_3862_);
v___x_3875_ = lean_nat_add(v___x_3832_, v_size_3850_);
if (lean_obj_tag(v_l_3854_) == 0)
{
lean_object* v_size_3885_; 
v_size_3885_ = lean_ctor_get(v_l_3854_, 0);
lean_inc(v_size_3885_);
v___y_3877_ = v_size_3885_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_unsigned_to_nat(0u);
v___y_3877_ = v___x_3886_;
goto v___jp_3876_;
}
v___jp_3864_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_nat_add(v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 4, v_impl_3831_);
lean_ctor_set(v___x_3860_, 3, v_r_3855_);
lean_ctor_set(v___x_3860_, 2, v_v_3339_);
lean_ctor_set(v___x_3860_, 1, v_k_3338_);
lean_ctor_set(v___x_3860_, 0, v___x_3868_);
v___x_3870_ = v___x_3860_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_r_3855_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v_impl_3831_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
lean_object* v___x_3872_; 
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 4, v___x_3870_);
lean_ctor_set(v___x_3848_, 3, v___y_3865_);
lean_ctor_set(v___x_3848_, 2, v_v_3853_);
lean_ctor_set(v___x_3848_, 1, v_k_3852_);
lean_ctor_set(v___x_3848_, 0, v___x_3863_);
v___x_3872_ = v___x_3848_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_k_3852_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_v_3853_);
lean_ctor_set(v_reuseFailAlloc_3873_, 3, v___y_3865_);
lean_ctor_set(v_reuseFailAlloc_3873_, 4, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
v___jp_3876_:
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
v___x_3878_ = lean_nat_add(v___x_3875_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec(v___x_3875_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_l_3854_);
lean_ctor_set(v___x_3343_, 3, v_l_3837_);
lean_ctor_set(v___x_3343_, 2, v_v_3836_);
lean_ctor_set(v___x_3343_, 1, v_k_3835_);
lean_ctor_set(v___x_3343_, 0, v___x_3878_);
v___x_3880_ = v___x_3343_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_k_3835_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_v_3836_);
lean_ctor_set(v_reuseFailAlloc_3884_, 3, v_l_3837_);
lean_ctor_set(v_reuseFailAlloc_3884_, 4, v_l_3854_);
v___x_3880_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_nat_add(v___x_3832_, v_size_3833_);
lean_dec(v_size_3833_);
if (lean_obj_tag(v_r_3855_) == 0)
{
lean_object* v_size_3882_; 
v_size_3882_ = lean_ctor_get(v_r_3855_, 0);
lean_inc(v_size_3882_);
v___y_3865_ = v___x_3880_;
v___y_3866_ = v___x_3881_;
v___y_3867_ = v_size_3882_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_unsigned_to_nat(0u);
v___y_3865_ = v___x_3880_;
v___y_3866_ = v___x_3881_;
v___y_3867_ = v___x_3883_;
goto v___jp_3864_;
}
}
}
}
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
lean_del_object(v___x_3343_);
v___x_3893_ = lean_nat_add(v___x_3832_, v_size_3834_);
lean_dec(v_size_3834_);
v___x_3894_ = lean_nat_add(v___x_3893_, v_size_3833_);
lean_dec(v___x_3893_);
v___x_3895_ = lean_nat_add(v___x_3832_, v_size_3833_);
lean_dec(v_size_3833_);
v___x_3896_ = lean_nat_add(v___x_3895_, v_size_3851_);
lean_dec(v___x_3895_);
lean_inc_ref(v_impl_3831_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 4, v_impl_3831_);
lean_ctor_set(v___x_3848_, 3, v_r_3838_);
lean_ctor_set(v___x_3848_, 2, v_v_3339_);
lean_ctor_set(v___x_3848_, 1, v_k_3338_);
lean_ctor_set(v___x_3848_, 0, v___x_3896_);
v___x_3898_ = v___x_3848_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_r_3838_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_impl_3831_);
v___x_3898_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
v_isSharedCheck_3905_ = !lean_is_exclusive(v_impl_3831_);
if (v_isSharedCheck_3905_ == 0)
{
lean_object* v_unused_3906_; lean_object* v_unused_3907_; lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; 
v_unused_3906_ = lean_ctor_get(v_impl_3831_, 4);
lean_dec(v_unused_3906_);
v_unused_3907_ = lean_ctor_get(v_impl_3831_, 3);
lean_dec(v_unused_3907_);
v_unused_3908_ = lean_ctor_get(v_impl_3831_, 2);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_impl_3831_, 1);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_impl_3831_, 0);
lean_dec(v_unused_3910_);
v___x_3900_ = v_impl_3831_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_dec(v_impl_3831_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 4, v___x_3898_);
lean_ctor_set(v___x_3900_, 3, v_l_3837_);
lean_ctor_set(v___x_3900_, 2, v_v_3836_);
lean_ctor_set(v___x_3900_, 1, v_k_3835_);
lean_ctor_set(v___x_3900_, 0, v___x_3894_);
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v_k_3835_);
lean_ctor_set(v_reuseFailAlloc_3904_, 2, v_v_3836_);
lean_ctor_set(v_reuseFailAlloc_3904_, 3, v_l_3837_);
lean_ctor_set(v_reuseFailAlloc_3904_, 4, v___x_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
v_size_3918_ = lean_ctor_get(v_impl_3831_, 0);
lean_inc(v_size_3918_);
v___x_3919_ = lean_nat_add(v___x_3832_, v_size_3918_);
lean_dec(v_size_3918_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_impl_3831_);
lean_ctor_set(v___x_3343_, 0, v___x_3919_);
v___x_3921_ = v___x_3343_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3922_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3922_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3922_, 4, v_impl_3831_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
else
{
if (lean_obj_tag(v_l_3340_) == 0)
{
lean_object* v_l_3923_; 
v_l_3923_ = lean_ctor_get(v_l_3340_, 3);
if (lean_obj_tag(v_l_3923_) == 0)
{
lean_object* v_r_3924_; 
lean_inc_ref(v_l_3923_);
v_r_3924_ = lean_ctor_get(v_l_3340_, 4);
lean_inc(v_r_3924_);
if (lean_obj_tag(v_r_3924_) == 0)
{
lean_object* v_size_3925_; lean_object* v_k_3926_; lean_object* v_v_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3940_; 
v_size_3925_ = lean_ctor_get(v_l_3340_, 0);
v_k_3926_ = lean_ctor_get(v_l_3340_, 1);
v_v_3927_ = lean_ctor_get(v_l_3340_, 2);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3941_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3942_);
v___x_3929_ = v_l_3340_;
v_isShared_3930_ = v_isSharedCheck_3940_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_v_3927_);
lean_inc(v_k_3926_);
lean_inc(v_size_3925_);
lean_dec(v_l_3340_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3940_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v_size_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v_size_3931_ = lean_ctor_get(v_r_3924_, 0);
v___x_3932_ = lean_nat_add(v___x_3832_, v_size_3925_);
lean_dec(v_size_3925_);
v___x_3933_ = lean_nat_add(v___x_3832_, v_size_3931_);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 4, v_impl_3831_);
lean_ctor_set(v___x_3929_, 3, v_r_3924_);
lean_ctor_set(v___x_3929_, 2, v_v_3339_);
lean_ctor_set(v___x_3929_, 1, v_k_3338_);
lean_ctor_set(v___x_3929_, 0, v___x_3933_);
v___x_3935_ = v___x_3929_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v_r_3924_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_impl_3831_);
v___x_3935_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3937_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3935_);
lean_ctor_set(v___x_3343_, 3, v_l_3923_);
lean_ctor_set(v___x_3343_, 2, v_v_3927_);
lean_ctor_set(v___x_3343_, 1, v_k_3926_);
lean_ctor_set(v___x_3343_, 0, v___x_3932_);
v___x_3937_ = v___x_3343_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_k_3926_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_v_3927_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_l_3923_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_k_3943_; lean_object* v_v_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3955_; 
v_k_3943_ = lean_ctor_get(v_l_3340_, 1);
v_v_3944_ = lean_ctor_get(v_l_3340_, 2);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; 
v_unused_3956_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3958_);
v___x_3946_ = v_l_3340_;
v_isShared_3947_ = v_isSharedCheck_3955_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_v_3944_);
lean_inc(v_k_3943_);
lean_dec(v_l_3340_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3955_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3948_ = lean_unsigned_to_nat(3u);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 3, v_r_3924_);
lean_ctor_set(v___x_3946_, 2, v_v_3339_);
lean_ctor_set(v___x_3946_, 1, v_k_3338_);
lean_ctor_set(v___x_3946_, 0, v___x_3832_);
v___x_3950_ = v___x_3946_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v_r_3924_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v_r_3924_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3950_);
lean_ctor_set(v___x_3343_, 3, v_l_3923_);
lean_ctor_set(v___x_3343_, 2, v_v_3944_);
lean_ctor_set(v___x_3343_, 1, v_k_3943_);
lean_ctor_set(v___x_3343_, 0, v___x_3948_);
v___x_3952_ = v___x_3343_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_k_3943_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_v_3944_);
lean_ctor_set(v_reuseFailAlloc_3953_, 3, v_l_3923_);
lean_ctor_set(v_reuseFailAlloc_3953_, 4, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
else
{
lean_object* v_r_3959_; 
v_r_3959_ = lean_ctor_get(v_l_3340_, 4);
lean_inc(v_r_3959_);
if (lean_obj_tag(v_r_3959_) == 0)
{
lean_object* v_k_3960_; lean_object* v_v_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3984_; 
lean_inc(v_l_3923_);
v_k_3960_ = lean_ctor_get(v_l_3340_, 1);
v_v_3961_ = lean_ctor_get(v_l_3340_, 2);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_l_3340_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; lean_object* v_unused_3986_; lean_object* v_unused_3987_; 
v_unused_3985_ = lean_ctor_get(v_l_3340_, 4);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_l_3340_, 3);
lean_dec(v_unused_3986_);
v_unused_3987_ = lean_ctor_get(v_l_3340_, 0);
lean_dec(v_unused_3987_);
v___x_3963_ = v_l_3340_;
v_isShared_3964_ = v_isSharedCheck_3984_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_v_3961_);
lean_inc(v_k_3960_);
lean_dec(v_l_3340_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3984_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v_k_3965_; lean_object* v_v_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3980_; 
v_k_3965_ = lean_ctor_get(v_r_3959_, 1);
v_v_3966_ = lean_ctor_get(v_r_3959_, 2);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_r_3959_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; 
v_unused_3981_ = lean_ctor_get(v_r_3959_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_r_3959_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_r_3959_, 0);
lean_dec(v_unused_3983_);
v___x_3968_ = v_r_3959_;
v_isShared_3969_ = v_isSharedCheck_3980_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_v_3966_);
lean_inc(v_k_3965_);
lean_dec(v_r_3959_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3980_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3970_ = lean_unsigned_to_nat(3u);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 4, v_l_3923_);
lean_ctor_set(v___x_3968_, 3, v_l_3923_);
lean_ctor_set(v___x_3968_, 2, v_v_3961_);
lean_ctor_set(v___x_3968_, 1, v_k_3960_);
lean_ctor_set(v___x_3968_, 0, v___x_3832_);
v___x_3972_ = v___x_3968_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3960_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3961_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_l_3923_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_l_3923_);
v___x_3972_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3974_; 
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 4, v_l_3923_);
lean_ctor_set(v___x_3963_, 2, v_v_3339_);
lean_ctor_set(v___x_3963_, 1, v_k_3338_);
lean_ctor_set(v___x_3963_, 0, v___x_3832_);
v___x_3974_ = v___x_3963_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_l_3923_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v_l_3923_);
v___x_3974_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3974_);
lean_ctor_set(v___x_3343_, 3, v___x_3972_);
lean_ctor_set(v___x_3343_, 2, v_v_3966_);
lean_ctor_set(v___x_3343_, 1, v_k_3965_);
lean_ctor_set(v___x_3343_, 0, v___x_3970_);
v___x_3976_ = v___x_3343_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3965_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3966_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3988_ = lean_unsigned_to_nat(2u);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_r_3959_);
lean_ctor_set(v___x_3343_, 0, v___x_3988_);
v___x_3990_ = v___x_3343_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3991_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3991_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3991_, 4, v_r_3959_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v___x_3993_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_l_3340_);
lean_ctor_set(v___x_3343_, 0, v___x_3832_);
v___x_3993_ = v___x_3343_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_k_3338_);
lean_ctor_set(v_reuseFailAlloc_3994_, 2, v_v_3339_);
lean_ctor_set(v_reuseFailAlloc_3994_, 3, v_l_3340_);
lean_ctor_set(v_reuseFailAlloc_3994_, 4, v_l_3340_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
}
}
else
{
return v_t_3337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3997_, lean_object* v_t_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3997_, v_t_3998_);
lean_dec(v_k_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_4000_, lean_object* v_x_4001_){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_4000_, v_x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_4003_, lean_object* v_x_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_4003_, v_x_4004_);
lean_dec(v_declName_4003_);
return v_res_4005_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_4008_ = l_Lean_stringToMessageData(v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v___f_4017_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___x_4061_; lean_object* v_env_4062_; lean_object* v___x_4063_; 
lean_inc(v_declName_4009_);
v___f_4017_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4017_, 0, v_declName_4009_);
v___x_4061_ = lean_st_ref_get(v___y_4015_);
v_env_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc_ref(v_env_4062_);
lean_dec(v___x_4061_);
v___x_4063_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4062_, v_declName_4009_);
lean_dec_ref(v_env_4062_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_dec(v_declName_4009_);
v___y_4019_ = v___y_4013_;
v___y_4020_ = v___y_4015_;
goto v___jp_4018_;
}
else
{
uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec_ref_known(v___x_4063_, 1);
lean_dec_ref(v___f_4017_);
v___x_4064_ = 0;
v___x_4065_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_4066_ = l_Lean_MessageData_ofConstName(v_declName_4009_, v___x_4064_);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_4069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4069_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
return v___x_4070_;
}
v___jp_4018_:
{
lean_object* v___x_4021_; lean_object* v_env_4022_; lean_object* v_nextMacroScope_4023_; lean_object* v_ngen_4024_; lean_object* v_auxDeclNGen_4025_; lean_object* v_traceState_4026_; lean_object* v_messages_4027_; lean_object* v_infoState_4028_; lean_object* v_snapshotTasks_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4059_; 
v___x_4021_ = lean_st_ref_take(v___y_4020_);
v_env_4022_ = lean_ctor_get(v___x_4021_, 0);
v_nextMacroScope_4023_ = lean_ctor_get(v___x_4021_, 1);
v_ngen_4024_ = lean_ctor_get(v___x_4021_, 2);
v_auxDeclNGen_4025_ = lean_ctor_get(v___x_4021_, 3);
v_traceState_4026_ = lean_ctor_get(v___x_4021_, 4);
v_messages_4027_ = lean_ctor_get(v___x_4021_, 6);
v_infoState_4028_ = lean_ctor_get(v___x_4021_, 7);
v_snapshotTasks_4029_ = lean_ctor_get(v___x_4021_, 8);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4059_ == 0)
{
lean_object* v_unused_4060_; 
v_unused_4060_ = lean_ctor_get(v___x_4021_, 5);
lean_dec(v_unused_4060_);
v___x_4031_ = v___x_4021_;
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_snapshotTasks_4029_);
lean_inc(v_infoState_4028_);
lean_inc(v_messages_4027_);
lean_inc(v_traceState_4026_);
lean_inc(v_auxDeclNGen_4025_);
lean_inc(v_ngen_4024_);
lean_inc(v_nextMacroScope_4023_);
lean_inc(v_env_4022_);
lean_dec(v___x_4021_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4039_; 
v___x_4033_ = l_Lean_docStringExt;
v___x_4034_ = lean_box(2);
v___x_4035_ = lean_box(0);
v___x_4036_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_4033_, v_env_4022_, v___f_4017_, v___x_4034_, v___x_4035_);
v___x_4037_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 5, v___x_4037_);
lean_ctor_set(v___x_4031_, 0, v___x_4036_);
v___x_4039_ = v___x_4031_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4036_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_nextMacroScope_4023_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_ngen_4024_);
lean_ctor_set(v_reuseFailAlloc_4058_, 3, v_auxDeclNGen_4025_);
lean_ctor_set(v_reuseFailAlloc_4058_, 4, v_traceState_4026_);
lean_ctor_set(v_reuseFailAlloc_4058_, 5, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4058_, 6, v_messages_4027_);
lean_ctor_set(v_reuseFailAlloc_4058_, 7, v_infoState_4028_);
lean_ctor_set(v_reuseFailAlloc_4058_, 8, v_snapshotTasks_4029_);
v___x_4039_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v_mctx_4042_; lean_object* v_zetaDeltaFVarIds_4043_; lean_object* v_postponed_4044_; lean_object* v_diag_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4056_; 
v___x_4040_ = lean_st_ref_put(v___y_4020_, v___x_4039_);
v___x_4041_ = lean_st_ref_take(v___y_4019_);
v_mctx_4042_ = lean_ctor_get(v___x_4041_, 0);
v_zetaDeltaFVarIds_4043_ = lean_ctor_get(v___x_4041_, 2);
v_postponed_4044_ = lean_ctor_get(v___x_4041_, 3);
v_diag_4045_ = lean_ctor_get(v___x_4041_, 4);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4056_ == 0)
{
lean_object* v_unused_4057_; 
v_unused_4057_ = lean_ctor_get(v___x_4041_, 1);
lean_dec(v_unused_4057_);
v___x_4047_ = v___x_4041_;
v_isShared_4048_ = v_isSharedCheck_4056_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_diag_4045_);
lean_inc(v_postponed_4044_);
lean_inc(v_zetaDeltaFVarIds_4043_);
lean_inc(v_mctx_4042_);
lean_dec(v___x_4041_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4056_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4052_; 
v___x_4049_ = lean_box(0);
v___x_4050_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4050_);
v___x_4052_ = v___x_4047_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_mctx_4042_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4050_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_zetaDeltaFVarIds_4043_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v_postponed_4044_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_diag_4045_);
v___x_4052_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_st_ref_put(v___y_4019_, v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4049_);
return v___x_4054_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
return v_res_4079_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_4088_ = l_Lean_stringToMessageData(v___x_4087_);
return v___x_4088_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_4091_ = l_Lean_stringToMessageData(v___x_4090_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v___x_4100_; lean_object* v_env_4101_; lean_object* v_ref_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; 
v___x_4100_ = lean_st_ref_get(v_a_4098_);
v_env_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc_ref(v_env_4101_);
lean_dec(v___x_4100_);
v_ref_4102_ = lean_ctor_get(v_a_4097_, 2);
v___x_4103_ = 1;
lean_inc(v_declName_4092_);
v___x_4104_ = l_Lean_findInternalDocString_x3f(v_env_4101_, v_declName_4092_, v___x_4103_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
if (lean_obj_tag(v_a_4105_) == 1)
{
lean_object* v_val_4106_; 
v_val_4106_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_val_4106_);
lean_dec_ref_known(v_a_4105_, 1);
if (lean_obj_tag(v_val_4106_) == 0)
{
lean_object* v_val_4107_; lean_object* v___x_4109_; uint8_t v_isShared_4110_; uint8_t v_isSharedCheck_4128_; 
v_val_4107_ = lean_ctor_get(v_val_4106_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v_val_4106_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4109_ = v_val_4106_;
v_isShared_4110_ = v_isSharedCheck_4128_;
goto v_resetjp_4108_;
}
else
{
lean_inc(v_val_4107_);
lean_dec(v_val_4106_);
v___x_4109_ = lean_box(0);
v_isShared_4110_ = v_isSharedCheck_4128_;
goto v_resetjp_4108_;
}
v_resetjp_4108_:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_removeBuiltinDocString(v_declName_4092_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v___x_4112_; 
lean_dec_ref_known(v___x_4111_, 1);
lean_del_object(v___x_4109_);
lean_inc(v_declName_4092_);
v___x_4112_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_4092_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v___x_4113_; 
lean_dec_ref_known(v___x_4112_, 1);
v___x_4113_ = l_Lean_addVersoDocStringFromString(v_declName_4092_, v_val_4107_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4113_;
}
else
{
lean_dec(v_val_4107_);
lean_dec(v_declName_4092_);
return v___x_4112_;
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_val_4107_);
lean_dec(v_declName_4092_);
v_a_4114_ = lean_ctor_get(v___x_4111_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4111_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4116_ = v___x_4111_;
v_isShared_4117_ = v_isSharedCheck_4127_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4111_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4127_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4118_ = lean_io_error_to_string(v_a_4114_);
if (v_isShared_4110_ == 0)
{
lean_ctor_set_tag(v___x_4109_, 3);
lean_ctor_set(v___x_4109_, 0, v___x_4118_);
v___x_4120_ = v___x_4109_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4124_; 
v___x_4121_ = l_Lean_MessageData_ofFormat(v___x_4120_);
lean_inc(v_ref_4102_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_ref_4102_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4122_);
v___x_4124_ = v___x_4116_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
}
else
{
lean_object* v___x_4129_; uint8_t v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec(v_val_4106_);
v___x_4129_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_4130_ = 0;
v___x_4131_ = l_Lean_MessageData_ofConstName(v_declName_4092_, v___x_4130_);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4129_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4134_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4135_;
}
}
else
{
lean_object* v___x_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
lean_dec(v_a_4105_);
v___x_4136_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_4137_ = 0;
v___x_4138_ = l_Lean_MessageData_ofConstName(v_declName_4092_, v___x_4137_);
v___x_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4136_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4139_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4141_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4142_;
}
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_declName_4092_);
v_a_4143_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4145_ = v___x_4104_;
v_isShared_4146_ = v_isSharedCheck_4154_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4104_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4154_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4147_ = lean_io_error_to_string(v_a_4143_);
v___x_4148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = l_Lean_MessageData_ofFormat(v___x_4148_);
lean_inc(v_ref_4102_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v_ref_4102_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 0, v___x_4150_);
v___x_4152_ = v___x_4145_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_makeDocStringVerso(v_declName_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_4164_, lean_object* v_k_4165_, lean_object* v_t_4166_, lean_object* v_h_4167_){
_start:
{
lean_object* v___x_4168_; 
v___x_4168_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_4165_, v_t_4166_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4169_, lean_object* v_k_4170_, lean_object* v_t_4171_, lean_object* v_h_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_4169_, v_k_4170_, v_t_4171_, v_h_4172_);
lean_dec(v_k_4170_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_4174_, lean_object* v_binders_4175_, lean_object* v_docComment_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
uint8_t v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = l_Lean_isVersoDocComment(v_docComment_4176_);
v___x_4185_ = l_Lean_addDocStringOf(v___x_4184_, v_declName_4174_, v_binders_4175_, v_docComment_4176_, v_a_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_4186_, lean_object* v_binders_4187_, lean_object* v_docComment_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_addDocString(v_declName_4186_, v_binders_4187_, v_docComment_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_4197_, lean_object* v_binders_4198_, lean_object* v_docString_x3f_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_){
_start:
{
if (lean_obj_tag(v_docString_x3f_4199_) == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_dec(v_binders_4198_);
lean_dec(v_declName_4197_);
v___x_4207_ = lean_box(0);
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
return v___x_4208_;
}
else
{
lean_object* v_val_4209_; lean_object* v___x_4210_; 
v_val_4209_ = lean_ctor_get(v_docString_x3f_4199_, 0);
lean_inc(v_val_4209_);
lean_dec_ref_known(v_docString_x3f_4199_, 1);
v___x_4210_ = l_Lean_addDocString(v_declName_4197_, v_binders_4198_, v_val_4209_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_4211_, lean_object* v_binders_4212_, lean_object* v_docString_x3f_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_addDocString_x27(v_declName_4211_, v_binders_4212_, v_docString_x3f_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v_nextMacroScope_4227_; lean_object* v_ngen_4228_; lean_object* v_auxDeclNGen_4229_; lean_object* v_traceState_4230_; lean_object* v_messages_4231_; lean_object* v_infoState_4232_; lean_object* v_snapshotTasks_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4259_; 
v___x_4226_ = lean_st_ref_take(v___y_4224_);
v_nextMacroScope_4227_ = lean_ctor_get(v___x_4226_, 1);
v_ngen_4228_ = lean_ctor_get(v___x_4226_, 2);
v_auxDeclNGen_4229_ = lean_ctor_get(v___x_4226_, 3);
v_traceState_4230_ = lean_ctor_get(v___x_4226_, 4);
v_messages_4231_ = lean_ctor_get(v___x_4226_, 6);
v_infoState_4232_ = lean_ctor_get(v___x_4226_, 7);
v_snapshotTasks_4233_ = lean_ctor_get(v___x_4226_, 8);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4259_ == 0)
{
lean_object* v_unused_4260_; lean_object* v_unused_4261_; 
v_unused_4260_ = lean_ctor_get(v___x_4226_, 5);
lean_dec(v_unused_4260_);
v_unused_4261_ = lean_ctor_get(v___x_4226_, 0);
lean_dec(v_unused_4261_);
v___x_4235_ = v___x_4226_;
v_isShared_4236_ = v_isSharedCheck_4259_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_snapshotTasks_4233_);
lean_inc(v_infoState_4232_);
lean_inc(v_messages_4231_);
lean_inc(v_traceState_4230_);
lean_inc(v_auxDeclNGen_4229_);
lean_inc(v_ngen_4228_);
lean_inc(v_nextMacroScope_4227_);
lean_dec(v___x_4226_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4259_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4237_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 5, v___x_4237_);
lean_ctor_set(v___x_4235_, 0, v_env_4222_);
v___x_4239_ = v___x_4235_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_env_4222_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v_nextMacroScope_4227_);
lean_ctor_set(v_reuseFailAlloc_4258_, 2, v_ngen_4228_);
lean_ctor_set(v_reuseFailAlloc_4258_, 3, v_auxDeclNGen_4229_);
lean_ctor_set(v_reuseFailAlloc_4258_, 4, v_traceState_4230_);
lean_ctor_set(v_reuseFailAlloc_4258_, 5, v___x_4237_);
lean_ctor_set(v_reuseFailAlloc_4258_, 6, v_messages_4231_);
lean_ctor_set(v_reuseFailAlloc_4258_, 7, v_infoState_4232_);
lean_ctor_set(v_reuseFailAlloc_4258_, 8, v_snapshotTasks_4233_);
v___x_4239_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v_mctx_4242_; lean_object* v_zetaDeltaFVarIds_4243_; lean_object* v_postponed_4244_; lean_object* v_diag_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4256_; 
v___x_4240_ = lean_st_ref_put(v___y_4224_, v___x_4239_);
v___x_4241_ = lean_st_ref_take(v___y_4223_);
v_mctx_4242_ = lean_ctor_get(v___x_4241_, 0);
v_zetaDeltaFVarIds_4243_ = lean_ctor_get(v___x_4241_, 2);
v_postponed_4244_ = lean_ctor_get(v___x_4241_, 3);
v_diag_4245_ = lean_ctor_get(v___x_4241_, 4);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4256_ == 0)
{
lean_object* v_unused_4257_; 
v_unused_4257_ = lean_ctor_get(v___x_4241_, 1);
lean_dec(v_unused_4257_);
v___x_4247_ = v___x_4241_;
v_isShared_4248_ = v_isSharedCheck_4256_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_diag_4245_);
lean_inc(v_postponed_4244_);
lean_inc(v_zetaDeltaFVarIds_4243_);
lean_inc(v_mctx_4242_);
lean_dec(v___x_4241_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4256_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4252_; 
v___x_4249_ = lean_box(0);
v___x_4250_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 1, v___x_4250_);
v___x_4252_ = v___x_4247_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_mctx_4242_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v___x_4250_);
lean_ctor_set(v_reuseFailAlloc_4255_, 2, v_zetaDeltaFVarIds_4243_);
lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_postponed_4244_);
lean_ctor_set(v_reuseFailAlloc_4255_, 4, v_diag_4245_);
v___x_4252_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4253_ = lean_st_ref_put(v___y_4223_, v___x_4252_);
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4249_);
return v___x_4254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec(v___y_4263_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_4267_, lean_object* v_as_4268_, size_t v_i_4269_, size_t v_stop_4270_, lean_object* v_b_4271_){
_start:
{
uint8_t v___x_4272_; 
v___x_4272_ = lean_usize_dec_eq(v_i_4269_, v_stop_4270_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v_index_4274_; lean_object* v_sourceString_4275_; lean_object* v_imports_4276_; lean_object* v_currNamespace_4277_; lean_object* v_openDecls_4278_; lean_object* v_options_4279_; lean_object* v_check_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4296_; 
v___x_4273_ = lean_array_uget(v_as_4268_, v_i_4269_);
v_index_4274_ = lean_ctor_get(v___x_4273_, 1);
v_sourceString_4275_ = lean_ctor_get(v___x_4273_, 2);
v_imports_4276_ = lean_ctor_get(v___x_4273_, 3);
v_currNamespace_4277_ = lean_ctor_get(v___x_4273_, 4);
v_openDecls_4278_ = lean_ctor_get(v___x_4273_, 5);
v_options_4279_ = lean_ctor_get(v___x_4273_, 6);
v_check_4280_ = lean_ctor_get(v___x_4273_, 7);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v___x_4273_, 0);
lean_dec(v_unused_4297_);
v___x_4282_ = v___x_4273_;
v_isShared_4283_ = v_isSharedCheck_4296_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_check_4280_);
lean_inc(v_options_4279_);
lean_inc(v_openDecls_4278_);
lean_inc(v_currNamespace_4277_);
lean_inc(v_imports_4276_);
lean_inc(v_sourceString_4275_);
lean_inc(v_index_4274_);
lean_dec(v___x_4273_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4296_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; lean_object* v_toEnvExtension_4285_; lean_object* v_asyncMode_4286_; lean_object* v___x_4287_; lean_object* v___x_4289_; 
v___x_4284_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_4285_ = lean_ctor_get(v___x_4284_, 0);
v_asyncMode_4286_ = lean_ctor_get(v_toEnvExtension_4285_, 2);
lean_inc(v_n_4267_);
v___x_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4287_, 0, v_n_4267_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4287_);
v___x_4289_ = v___x_4282_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_index_4274_);
lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_sourceString_4275_);
lean_ctor_set(v_reuseFailAlloc_4295_, 3, v_imports_4276_);
lean_ctor_set(v_reuseFailAlloc_4295_, 4, v_currNamespace_4277_);
lean_ctor_set(v_reuseFailAlloc_4295_, 5, v_openDecls_4278_);
lean_ctor_set(v_reuseFailAlloc_4295_, 6, v_options_4279_);
lean_ctor_set(v_reuseFailAlloc_4295_, 7, v_check_4280_);
v___x_4289_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; size_t v___x_4292_; size_t v___x_4293_; 
v___x_4290_ = lean_box(0);
v___x_4291_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4284_, v_b_4271_, v___x_4289_, v_asyncMode_4286_, v___x_4290_);
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_add(v_i_4269_, v___x_4292_);
v_i_4269_ = v___x_4293_;
v_b_4271_ = v___x_4291_;
goto _start;
}
}
}
else
{
lean_dec(v_n_4267_);
return v_b_4271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_4298_, lean_object* v_as_4299_, lean_object* v_i_4300_, lean_object* v_stop_4301_, lean_object* v_b_4302_){
_start:
{
size_t v_i_boxed_4303_; size_t v_stop_boxed_4304_; lean_object* v_res_4305_; 
v_i_boxed_4303_ = lean_unbox_usize(v_i_4300_);
lean_dec(v_i_4300_);
v_stop_boxed_4304_ = lean_unbox_usize(v_stop_4301_);
lean_dec(v_stop_4301_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_4298_, v_as_4299_, v_i_boxed_4303_, v_stop_boxed_4304_, v_b_4302_);
lean_dec_ref(v_as_4299_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_4306_, lean_object* v_deferred_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v_env_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4315_ = lean_st_ref_get(v___y_4313_);
v_env_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_ref(v_env_4316_);
lean_dec(v___x_4315_);
v___x_4317_ = l_Lean_getMainModuleDoc(v_env_4316_);
v___x_4318_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_4317_);
lean_dec_ref(v___x_4317_);
if (v___x_4318_ == 0)
{
lean_object* v___x_4319_; lean_object* v___x_4320_; 
lean_dec_ref(v_docs_4306_);
v___x_4319_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_4320_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4319_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; lean_object* v_env_4322_; lean_object* v___x_4323_; lean_object* v_size_4324_; lean_object* v___x_4325_; lean_object* v_env_4326_; lean_object* v___x_4327_; 
v___x_4321_ = lean_st_ref_get(v___y_4313_);
v_env_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc_ref(v_env_4322_);
lean_dec(v___x_4321_);
v___x_4323_ = l_Lean_getMainVersoModuleDocs(v_env_4322_);
v_size_4324_ = lean_ctor_get(v___x_4323_, 2);
lean_inc(v_size_4324_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = lean_st_ref_get(v___y_4313_);
v_env_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_ref(v_env_4326_);
lean_dec(v___x_4325_);
v___x_4327_ = l_Lean_addVersoModuleDocSnippet(v_env_4326_, v_docs_4306_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
lean_dec(v_size_4324_);
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4329_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_4330_ = l_Lean_stringToMessageData(v_a_4328_);
v___x_4331_ = l_Lean_indentD(v___x_4330_);
v___x_4332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4329_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
v___x_4333_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_parseVersoDocString___at___00Lean_versoDocString_spec__0_spec__1_spec__2___redArg(v___x_4332_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
return v___x_4333_;
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v_a_4334_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4327_, 1);
v___x_4335_ = lean_unsigned_to_nat(0u);
v___x_4336_ = lean_array_get_size(v_deferred_4307_);
v___x_4337_ = lean_nat_dec_lt(v___x_4335_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec(v_size_4324_);
v___x_4338_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_4334_, v___y_4311_, v___y_4313_);
return v___x_4338_;
}
else
{
size_t v___x_4339_; size_t v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4339_ = ((size_t)0ULL);
v___x_4340_ = lean_usize_of_nat(v___x_4336_);
v___x_4341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_4324_, v_deferred_4307_, v___x_4339_, v___x_4340_, v_a_4334_);
v___x_4342_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_4341_, v___y_4311_, v___y_4313_);
return v___x_4342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_4343_, lean_object* v_deferred_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_4343_, v_deferred_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec_ref(v_deferred_4344_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_4353_, lean_object* v_docComment_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_versoModDocString(v_range_4353_, v_docComment_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v_fst_4364_; lean_object* v_snd_4365_; lean_object* v___x_4366_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v_fst_4364_ = lean_ctor_get(v_a_4363_, 0);
lean_inc(v_fst_4364_);
v_snd_4365_ = lean_ctor_get(v_a_4363_, 1);
lean_inc(v_snd_4365_);
lean_dec(v_a_4363_);
v___x_4366_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_4364_, v_snd_4365_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
lean_dec(v_snd_4365_);
return v___x_4366_;
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_a_4367_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4362_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4362_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_4375_, lean_object* v_docComment_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_addVersoModDocString(v_range_4375_, v_docComment_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_);
lean_dec(v_a_4382_);
lean_dec_ref(v_a_4381_);
lean_dec(v_a_4380_);
lean_dec_ref(v_a_4379_);
lean_dec(v_a_4378_);
lean_dec_ref(v_a_4377_);
lean_dec(v_docComment_4376_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; 
v___x_4393_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_4385_, v___y_4389_, v___y_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
return v_res_4402_;
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
