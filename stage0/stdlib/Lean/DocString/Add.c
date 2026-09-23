// Lean compiler output
// Module: Lean.DocString.Add
// Imports: import Lean.Elab.DocString public import Lean.DocString.DeferredCheck public import Lean.DocString.Types import Lean.DocString.Parser public import Lean.Elab.Term.TermElabM
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_BlockCtxt_forDocString(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Doc_Parser_documentFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Doc_Parser_locateError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Error_toString(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Doc_parseFailureKind;
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
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
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = " of this documentation comment has no source location, so it cannot be parsed."};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "closing delimiter"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "content"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5;
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "opening delimiter"};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "This documentation comment has an unexpected structure, so it cannot be parsed."};
static const lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0 = (const lean_object*)&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_versoDocStringOfText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocStringOfText___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_versoDocStringOfText___closed__1 = (const lean_object*)&l_Lean_versoDocStringOfText___closed__1_value;
static const lean_closure_object l_Lean_versoDocStringOfText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_documentFn, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_versoDocStringOfText___closed__1_value)} };
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
static const lean_string_object l_Lean_versoDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_versoDocString___closed__0 = (const lean_object*)&l_Lean_versoDocString___closed__0_value;
static const lean_string_object l_Lean_versoDocString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_versoDocString___closed__1 = (const lean_object*)&l_Lean_versoDocString___closed__1_value;
static const lean_string_object l_Lean_versoDocString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_versoDocString___closed__2 = (const lean_object*)&l_Lean_versoDocString___closed__2_value;
static const lean_string_object l_Lean_versoDocString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_versoDocString___closed__3 = (const lean_object*)&l_Lean_versoDocString___closed__3_value;
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_versoDocString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_0),((lean_object*)&l_Lean_versoDocString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_1),((lean_object*)&l_Lean_versoDocString___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_versoDocString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_versoDocString___closed__4_value_aux_2),((lean_object*)&l_Lean_versoDocString___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 150, 193, 173, 39, 149, 4, 235)}};
static const lean_object* l_Lean_versoDocString___closed__4 = (const lean_object*)&l_Lean_versoDocString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(lean_object* v_ictx_134_, lean_object* v_pos_135_, lean_object* v_e_136_){
_start:
{
lean_object* v___x_137_; lean_object* v_snd_138_; lean_object* v_fst_139_; lean_object* v_fst_140_; lean_object* v_snd_141_; lean_object* v_fileName_142_; lean_object* v_fileMap_143_; lean_object* v___x_144_; lean_object* v___y_146_; 
v___x_137_ = l_Lean_Doc_Parser_locateError(v_ictx_134_, v_pos_135_, v_e_136_);
v_snd_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_snd_138_);
v_fst_139_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_fst_139_);
lean_dec_ref(v___x_137_);
v_fst_140_ = lean_ctor_get(v_snd_138_, 0);
lean_inc(v_fst_140_);
v_snd_141_ = lean_ctor_get(v_snd_138_, 1);
lean_inc(v_snd_141_);
lean_dec(v_snd_138_);
v_fileName_142_ = lean_ctor_get(v_ictx_134_, 1);
lean_inc_ref(v_fileName_142_);
v_fileMap_143_ = lean_ctor_get(v_ictx_134_, 2);
lean_inc_ref_n(v_fileMap_143_, 2);
lean_dec_ref(v_ictx_134_);
v___x_144_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v_fst_139_);
lean_dec(v_fst_139_);
if (lean_obj_tag(v_fst_140_) == 0)
{
lean_object* v___x_155_; 
lean_dec_ref(v_fileMap_143_);
v___x_155_ = lean_box(0);
v___y_146_ = v___x_155_;
goto v___jp_145_;
}
else
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_164_; 
v_val_156_ = lean_ctor_get(v_fst_140_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v_fst_140_);
if (v_isSharedCheck_164_ == 0)
{
v___x_158_ = v_fst_140_;
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_fst_140_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_164_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = l_Lean_FileMap_toPosition(v_fileMap_143_, v_val_156_);
lean_dec(v_val_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 0, v___x_160_);
v___x_162_ = v___x_158_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
v___y_146_ = v___x_162_;
goto v___jp_145_;
}
}
}
v___jp_145_:
{
uint8_t v___x_147_; uint8_t v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_147_ = 1;
v___x_148_ = 2;
v___x_149_ = 0;
v___x_150_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
v___x_151_ = l_Lean_Parser_Error_toString(v_snd_141_);
v___x_152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
v___x_153_ = l_Lean_MessageData_ofFormat(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_154_, 0, v_fileName_142_);
lean_ctor_set(v___x_154_, 1, v___x_144_);
lean_ctor_set(v___x_154_, 2, v___y_146_);
lean_ctor_set(v___x_154_, 3, v___x_150_);
lean_ctor_set(v___x_154_, 4, v___x_153_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5, v___x_147_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5 + 1, v___x_148_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*5 + 2, v___x_149_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx(lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_unsigned_to_nat(0u);
return v___x_166_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_unsigned_to_nat(1u);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_VersoDocstringMarkup_ctorIdx(v_x_168_);
lean_dec_ref(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___redArg(lean_object* v_t_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_doc_172_; lean_object* v___x_173_; 
v_doc_172_ = lean_ctor_get(v_t_170_, 0);
lean_inc(v_doc_172_);
lean_dec_ref(v_t_170_);
v___x_173_ = lean_apply_1(v_k_171_, v_doc_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim(lean_object* v_motive_174_, lean_object* v_ctorIdx_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_k_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_176_, v_k_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___boxed(lean_object* v_motive_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_VersoDocstringMarkup_ctorElim(v_motive_180_, v_ctorIdx_181_, v_t_182_, v_h_183_, v_k_184_);
lean_dec(v_ctorIdx_181_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim___redArg(lean_object* v_t_186_, lean_object* v_document_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_186_, v_document_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim(lean_object* v_motive_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_document_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_190_, v_document_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim___redArg(lean_object* v_t_194_, lean_object* v_parseFailure_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_194_, v_parseFailure_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_parseFailure_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_198_, v_parseFailure_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx(lean_object* v_x_202_){
_start:
{
lean_object* v_doc_203_; 
v_doc_203_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_doc_203_);
return v_doc_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx___boxed(lean_object* v_x_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_VersoDocstringMarkup_stx(v_x_204_);
lean_dec_ref(v_x_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object* v_docComment_206_){
_start:
{
lean_object* v___x_207_; lean_object* v_body_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___y_212_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v_body_208_ = l_Lean_Syntax_getArg(v_docComment_206_, v___x_207_);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = l_Lean_Syntax_getArg(v_docComment_206_, v___x_209_);
v___x_215_ = l_Lean_Syntax_getArg(v_body_208_, v___x_209_);
v___x_216_ = l_Lean_Doc_parseFailureKind;
lean_inc(v___x_215_);
v___x_217_ = l_Lean_Syntax_isOfKind(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_215_);
v___y_212_ = v___x_218_;
goto v___jp_211_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_Lean_Syntax_getArg(v___x_215_, v___x_209_);
lean_dec(v___x_215_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
v___y_212_ = v___x_220_;
goto v___jp_211_;
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = l_Lean_Syntax_getArg(v_body_208_, v___x_207_);
lean_dec(v_body_208_);
v___x_214_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_214_, 0, v___x_210_);
lean_ctor_set(v___x_214_, 1, v___y_212_);
lean_ctor_set(v___x_214_, 2, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object* v_docComment_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_VersoDocstringView_of(v_docComment_221_);
lean_dec(v_docComment_221_);
return v_res_222_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation(lean_object* v_what_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_230_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1);
v___x_231_ = l_Lean_stringToMessageData(v_what_229_);
v___x_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0));
v___x_237_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3));
v___x_242_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6));
v___x_247_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange(lean_object* v_view_250_){
_start:
{
lean_object* v_opener_251_; lean_object* v_markup_252_; lean_object* v_closer_253_; uint8_t v___x_254_; lean_object* v___x_255_; 
v_opener_251_ = lean_ctor_get(v_view_250_, 0);
v_markup_252_ = lean_ctor_get(v_view_250_, 1);
v_closer_253_ = lean_ctor_get(v_view_250_, 2);
v___x_254_ = 1;
v___x_255_ = l_Lean_Syntax_getPos_x3f(v_opener_251_, v___x_254_);
if (lean_obj_tag(v___x_255_) == 1)
{
lean_object* v_val_256_; lean_object* v___y_258_; lean_object* v_doc_274_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v_doc_274_ = lean_ctor_get(v_markup_252_, 0);
v___y_258_ = v_doc_274_;
goto v___jp_257_;
v___jp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Syntax_getPos_x3f(v___y_258_, v___x_254_);
if (lean_obj_tag(v___x_259_) == 1)
{
lean_object* v_val_260_; lean_object* v___x_261_; 
v_val_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_val_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = l_Lean_Syntax_getPos_x3f(v_closer_253_, v___x_254_);
if (lean_obj_tag(v___x_261_) == 1)
{
lean_object* v_val_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_271_; 
v_val_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_271_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_271_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_val_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_271_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_val_260_);
lean_ctor_set(v___x_266_, 1, v_val_262_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v_val_256_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v___x_261_);
lean_dec(v_val_260_);
lean_dec(v_val_256_);
v___x_272_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_272_;
}
}
else
{
lean_object* v___x_273_; 
lean_dec(v___x_259_);
lean_dec(v_val_256_);
v___x_273_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_273_;
}
}
}
else
{
lean_object* v___x_275_; 
lean_dec(v___x_255_);
v___x_275_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___boxed(lean_object* v_view_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_276_);
lean_dec_ref(v_view_276_);
return v_res_277_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0));
v___x_280_ = l_Lean_stringToMessageData(v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object* v_docComment_283_){
_start:
{
if (lean_obj_tag(v_docComment_283_) == 1)
{
lean_object* v_args_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_args_286_ = lean_ctor_get(v_docComment_283_, 2);
v___x_287_ = lean_array_get_size(v_args_286_);
v___x_288_ = lean_unsigned_to_nat(2u);
v___x_289_ = lean_nat_dec_eq(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
goto v___jp_284_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = lean_array_fget_borrowed(v_args_286_, v___x_290_);
if (lean_obj_tag(v___x_291_) == 1)
{
lean_object* v_args_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_args_292_ = lean_ctor_get(v___x_291_, 2);
v___x_293_ = lean_array_get_size(v_args_292_);
v___x_294_ = lean_nat_dec_eq(v___x_293_, v___x_288_);
if (v___x_294_ == 0)
{
goto v___jp_284_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_array_fget_borrowed(v_args_286_, v___x_295_);
v___x_297_ = l_Lean_Syntax_getPos_x3f(v___x_296_, v___x_294_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_val_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = lean_array_fget_borrowed(v_args_292_, v___x_295_);
v___x_300_ = l_Lean_Syntax_getPos_x3f(v___x_299_, v___x_294_);
if (lean_obj_tag(v___x_300_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_val_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = lean_array_fget_borrowed(v_args_292_, v___x_290_);
v___x_303_ = l_Lean_Syntax_getPos_x3f(v___x_302_, v___x_294_);
if (lean_obj_tag(v___x_303_) == 1)
{
lean_object* v_val_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_313_; 
v_val_304_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_313_ == 0)
{
v___x_306_ = v___x_303_;
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_val_304_);
lean_dec(v___x_303_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_313_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_val_301_);
lean_ctor_set(v___x_308_, 1, v_val_304_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_val_298_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v___x_309_);
v___x_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
else
{
lean_object* v___x_314_; 
lean_dec(v___x_303_);
lean_dec(v_val_301_);
lean_dec(v_val_298_);
v___x_314_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_314_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v___x_300_);
lean_dec(v_val_298_);
v___x_315_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_315_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec(v___x_297_);
v___x_316_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_316_;
}
}
}
else
{
goto v___jp_284_;
}
}
}
else
{
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___boxed(lean_object* v_docComment_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_317_);
lean_dec(v_docComment_317_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(uint8_t v_suppressElabErrors_327_, uint8_t v___x_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 1)
{
lean_object* v_pre_330_; 
v_pre_330_ = lean_ctor_get(v_x_329_, 0);
switch(lean_obj_tag(v_pre_330_))
{
case 1:
{
lean_object* v_pre_331_; 
v_pre_331_ = lean_ctor_get(v_pre_330_, 0);
switch(lean_obj_tag(v_pre_331_))
{
case 0:
{
lean_object* v_str_332_; lean_object* v_str_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_str_332_ = lean_ctor_get(v_x_329_, 1);
v_str_333_ = lean_ctor_get(v_pre_330_, 1);
v___x_334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_335_ = lean_string_dec_eq(v_str_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_337_ = lean_string_dec_eq(v_str_333_, v___x_336_);
if (v___x_337_ == 0)
{
return v___x_337_;
}
else
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_339_ = lean_string_dec_eq(v_str_332_, v___x_338_);
if (v___x_339_ == 0)
{
return v___x_339_;
}
else
{
return v_suppressElabErrors_327_;
}
}
}
else
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_341_ = lean_string_dec_eq(v_str_332_, v___x_340_);
if (v___x_341_ == 0)
{
return v___x_341_;
}
else
{
return v_suppressElabErrors_327_;
}
}
}
case 1:
{
lean_object* v_pre_342_; 
v_pre_342_ = lean_ctor_get(v_pre_331_, 0);
if (lean_obj_tag(v_pre_342_) == 0)
{
lean_object* v_str_343_; lean_object* v_str_344_; lean_object* v_str_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_str_343_ = lean_ctor_get(v_x_329_, 1);
v_str_344_ = lean_ctor_get(v_pre_330_, 1);
v_str_345_ = lean_ctor_get(v_pre_331_, 1);
v___x_346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_347_ = lean_string_dec_eq(v_str_345_, v___x_346_);
if (v___x_347_ == 0)
{
return v___x_347_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_349_ = lean_string_dec_eq(v_str_344_, v___x_348_);
if (v___x_349_ == 0)
{
return v___x_349_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_351_ = lean_string_dec_eq(v_str_343_, v___x_350_);
if (v___x_351_ == 0)
{
return v___x_351_;
}
else
{
return v_suppressElabErrors_327_;
}
}
}
}
else
{
return v___x_328_;
}
}
default: 
{
return v___x_328_;
}
}
}
case 0:
{
lean_object* v_str_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_str_352_ = lean_ctor_get(v_x_329_, 1);
v___x_353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_354_ = lean_string_dec_eq(v_str_352_, v___x_353_);
if (v___x_354_ == 0)
{
return v___x_354_;
}
else
{
return v_suppressElabErrors_327_;
}
}
default: 
{
return v___x_328_;
}
}
}
else
{
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_355_, lean_object* v___x_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_suppressElabErrors_boxed_358_; uint8_t v___x_3702__boxed_359_; uint8_t v_res_360_; lean_object* v_r_361_; 
v_suppressElabErrors_boxed_358_ = lean_unbox(v_suppressElabErrors_355_);
v___x_3702__boxed_359_ = lean_unbox(v___x_356_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(v_suppressElabErrors_boxed_358_, v___x_3702__boxed_359_, v_x_357_);
lean_dec(v_x_357_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v_as_364_, size_t v_sz_365_, size_t v_i_366_, lean_object* v_b_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_a_372_; uint8_t v___x_376_; 
v___x_376_ = lean_usize_dec_lt(v_i_366_, v_sz_365_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec_ref(v___x_362_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v_b_367_);
return v___x_377_;
}
else
{
lean_object* v_a_378_; lean_object* v_snd_379_; lean_object* v_fst_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_446_; 
v_a_378_ = lean_array_uget(v_as_364_, v_i_366_);
v_snd_379_ = lean_ctor_get(v_a_378_, 1);
v_fst_380_ = lean_ctor_get(v_a_378_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_378_);
if (v_isSharedCheck_446_ == 0)
{
v___x_382_ = v_a_378_;
v_isShared_383_ = v_isSharedCheck_446_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_380_);
lean_dec(v_a_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_446_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_snd_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_444_; 
v_snd_384_ = lean_ctor_get(v_snd_379_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_snd_379_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_snd_379_, 0);
lean_dec(v_unused_445_);
v___x_386_ = v_snd_379_;
v_isShared_387_ = v_isSharedCheck_444_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snd_384_);
lean_dec(v_snd_379_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_444_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v_suppressElabErrors_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___y_392_; lean_object* v___y_393_; 
v_suppressElabErrors_388_ = lean_ctor_get_uint8(v___y_368_, sizeof(void*)*3 + 1);
v___x_389_ = lean_box(0);
lean_inc_ref(v___x_362_);
v___x_390_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v___x_362_, v_fst_380_, v_snd_384_);
if (v_suppressElabErrors_388_ == 0)
{
v___y_392_ = v___y_368_;
v___y_393_ = v___y_369_;
goto v___jp_391_;
}
else
{
lean_object* v_data_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; uint8_t v___x_443_; 
v_data_437_ = lean_ctor_get(v___x_390_, 4);
lean_inc(v_data_437_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_363_, v___x_438_);
v___x_440_ = lean_box(v_suppressElabErrors_388_);
v___x_441_ = lean_box(v___x_439_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_442_, 0, v___x_440_);
lean_closure_set(v___f_442_, 1, v___x_441_);
v___x_443_ = l_Lean_MessageData_hasTag(v___f_442_, v_data_437_);
if (v___x_443_ == 0)
{
lean_dec_ref(v___x_390_);
lean_del_object(v___x_386_);
lean_del_object(v___x_382_);
v_a_372_ = v___x_389_;
goto v___jp_371_;
}
else
{
v___y_392_ = v___y_368_;
v___y_393_ = v___y_369_;
goto v___jp_391_;
}
}
v___jp_391_:
{
lean_object* v_toCold_394_; lean_object* v_fileName_395_; lean_object* v_pos_396_; lean_object* v_endPos_397_; uint8_t v_keepFullRange_398_; uint8_t v_severity_399_; uint8_t v_isSilent_400_; lean_object* v_caption_401_; lean_object* v_data_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_436_; 
v_toCold_394_ = lean_ctor_get(v___y_392_, 0);
v_fileName_395_ = lean_ctor_get(v___x_390_, 0);
v_pos_396_ = lean_ctor_get(v___x_390_, 1);
v_endPos_397_ = lean_ctor_get(v___x_390_, 2);
v_keepFullRange_398_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5);
v_severity_399_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5 + 1);
v_isSilent_400_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5 + 2);
v_caption_401_ = lean_ctor_get(v___x_390_, 3);
v_data_402_ = lean_ctor_get(v___x_390_, 4);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_436_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_436_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_data_402_);
lean_inc(v_caption_401_);
lean_inc(v_endPos_397_);
lean_inc(v_pos_396_);
lean_inc(v_fileName_395_);
lean_dec(v___x_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_436_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_currNamespace_406_; lean_object* v_openDecls_407_; lean_object* v___x_409_; 
v_currNamespace_406_ = lean_ctor_get(v_toCold_394_, 4);
v_openDecls_407_ = lean_ctor_get(v_toCold_394_, 5);
lean_inc(v_openDecls_407_);
lean_inc(v_currNamespace_406_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_openDecls_407_);
lean_ctor_set(v___x_386_, 0, v_currNamespace_406_);
v___x_409_ = v___x_386_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_currNamespace_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_openDecls_407_);
v___x_409_ = v_reuseFailAlloc_435_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set_tag(v___x_382_, 4);
lean_ctor_set(v___x_382_, 1, v_data_402_);
lean_ctor_set(v___x_382_, 0, v___x_409_);
v___x_411_ = v___x_382_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_data_402_);
v___x_411_ = v_reuseFailAlloc_434_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 4, v___x_411_);
v___x_413_ = v___x_404_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fileName_395_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_pos_396_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_endPos_397_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_caption_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5, v_keepFullRange_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5 + 1, v_severity_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5 + 2, v_isSilent_400_);
v___x_413_ = v_reuseFailAlloc_433_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v_env_415_; lean_object* v_nextMacroScope_416_; lean_object* v_ngen_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_traceState_419_; lean_object* v_cache_420_; lean_object* v_messages_421_; lean_object* v_infoState_422_; lean_object* v_snapshotTasks_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
v___x_414_ = lean_st_ref_take(v___y_393_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
v_nextMacroScope_416_ = lean_ctor_get(v___x_414_, 1);
v_ngen_417_ = lean_ctor_get(v___x_414_, 2);
v_auxDeclNGen_418_ = lean_ctor_get(v___x_414_, 3);
v_traceState_419_ = lean_ctor_get(v___x_414_, 4);
v_cache_420_ = lean_ctor_get(v___x_414_, 5);
v_messages_421_ = lean_ctor_get(v___x_414_, 6);
v_infoState_422_ = lean_ctor_get(v___x_414_, 7);
v_snapshotTasks_423_ = lean_ctor_get(v___x_414_, 8);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_432_ == 0)
{
v___x_425_ = v___x_414_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snapshotTasks_423_);
lean_inc(v_infoState_422_);
lean_inc(v_messages_421_);
lean_inc(v_cache_420_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_418_);
lean_inc(v_ngen_417_);
lean_inc(v_nextMacroScope_416_);
lean_inc(v_env_415_);
lean_dec(v___x_414_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Lean_MessageLog_add(v___x_413_, v_messages_421_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 6, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_419_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_infoState_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_snapshotTasks_423_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_st_ref_put(v___y_393_, v___x_429_);
v_a_372_ = v___x_389_;
goto v___jp_371_;
}
}
}
}
}
}
}
}
}
}
v___jp_371_:
{
size_t v___x_373_; size_t v___x_374_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_366_, v___x_373_);
v_i_366_ = v___x_374_;
v_b_367_ = v_a_372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___boxed(lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v_as_449_, lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_457_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_447_, v___x_448_, v_as_449_, v_sz_boxed_456_, v_i_boxed_457_, v_b_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec_ref(v_as_449_);
lean_dec(v___x_448_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt(lean_object* v_openPos_459_, lean_object* v_startPos_460_, lean_object* v_endPos_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_toCold_465_; lean_object* v_fileMap_466_; lean_object* v_fileName_467_; lean_object* v_options_468_; lean_object* v_currNamespace_469_; lean_object* v_openDecls_470_; lean_object* v_source_471_; lean_object* v___y_473_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_toCold_465_ = lean_ctor_get(v_a_462_, 0);
v_fileMap_466_ = lean_ctor_get(v_toCold_465_, 1);
v_fileName_467_ = lean_ctor_get(v_toCold_465_, 0);
v_options_468_ = lean_ctor_get(v_toCold_465_, 2);
v_currNamespace_469_ = lean_ctor_get(v_toCold_465_, 4);
v_openDecls_470_ = lean_ctor_get(v_toCold_465_, 5);
v_source_471_ = lean_ctor_get(v_fileMap_466_, 0);
v___x_513_ = lean_string_utf8_byte_size(v_source_471_);
v___x_514_ = lean_nat_dec_le(v_endPos_461_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_endPos_461_);
v___y_473_ = v___x_513_;
goto v___jp_472_;
}
else
{
v___y_473_ = v_endPos_461_;
goto v___jp_472_;
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v_env_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_474_ = lean_st_ref_get(v_a_463_);
v_env_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref_n(v_env_475_, 2);
lean_dec(v___x_474_);
lean_inc(v___y_473_);
lean_inc_ref_n(v_fileMap_466_, 2);
lean_inc_ref(v_fileName_467_);
lean_inc_ref(v_source_471_);
v___x_476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_476_, 0, v_source_471_);
lean_ctor_set(v___x_476_, 1, v_fileName_467_);
lean_ctor_set(v___x_476_, 2, v_fileMap_466_);
lean_ctor_set(v___x_476_, 3, v___y_473_);
lean_inc(v_openDecls_470_);
lean_inc(v_currNamespace_469_);
lean_inc_ref(v_options_468_);
v___x_477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_477_, 0, v_env_475_);
lean_ctor_set(v___x_477_, 1, v_options_468_);
lean_ctor_set(v___x_477_, 2, v_currNamespace_469_);
lean_ctor_set(v___x_477_, 3, v_openDecls_470_);
lean_inc(v_startPos_460_);
v___x_478_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_466_, v_openPos_459_, v_startPos_460_, v___y_473_);
v___x_479_ = l_Lean_Parser_mkParserState(v_source_471_);
v___x_480_ = l_Lean_Parser_ParserState_setPos(v___x_479_, v_startPos_460_);
v___x_481_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_481_, 0, v___x_478_);
v___x_482_ = l_Lean_Parser_getTokenTable(v_env_475_);
lean_inc_ref(v___x_476_);
v___x_483_ = l_Lean_Parser_ParserFn_run(v___x_481_, v___x_476_, v___x_477_, v___x_482_, v___x_480_);
lean_inc_ref(v___x_483_);
v___x_484_ = l_Lean_Parser_ParserState_allErrors(v___x_483_);
v___x_485_ = lean_array_get_size(v___x_484_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; size_t v_sz_489_; size_t v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v___x_483_);
v___x_488_ = lean_box(0);
v_sz_489_ = lean_array_size(v___x_484_);
v___x_490_ = ((size_t)0ULL);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_476_, v___x_485_, v___x_484_, v_sz_489_, v___x_490_, v___x_488_, v_a_462_, v_a_463_);
lean_dec_ref(v___x_484_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_500_);
v___x_493_ = v___x_491_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_dec(v___x_491_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_a_501_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_491_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_491_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_stxStack_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec_ref(v___x_484_);
lean_dec_ref_known(v___x_476_, 4);
v_stxStack_509_ = lean_ctor_get(v___x_483_, 0);
lean_inc_ref(v_stxStack_509_);
lean_dec_ref(v___x_483_);
v___x_510_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_509_);
lean_dec_ref(v_stxStack_509_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt___boxed(lean_object* v_openPos_515_, lean_object* v_startPos_516_, lean_object* v_endPos_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_parseVersoDocStringAt(v_openPos_515_, v_startPos_516_, v_endPos_517_, v_a_518_, v_a_519_);
lean_dec(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_openPos_515_);
return v_res_521_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_522_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_ctor_set(v___x_527_, 2, v___x_526_);
lean_ctor_set(v___x_527_, 3, v___x_526_);
lean_ctor_set(v___x_527_, 4, v___x_525_);
lean_ctor_set(v___x_527_, 5, v___x_525_);
lean_ctor_set(v___x_527_, 6, v___x_525_);
lean_ctor_set(v___x_527_, 7, v___x_525_);
lean_ctor_set(v___x_527_, 8, v___x_525_);
lean_ctor_set(v___x_527_, 9, v___x_525_);
lean_ctor_set(v___x_527_, 10, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_unsigned_to_nat(32u);
v___x_529_ = lean_mk_empty_array_with_capacity(v___x_528_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_531_ = ((size_t)5ULL);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_unsigned_to_nat(32u);
v___x_534_ = lean_mk_empty_array_with_capacity(v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3);
v___x_536_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_532_);
lean_ctor_set(v___x_536_, 3, v___x_532_);
lean_ctor_set_usize(v___x_536_, 4, v___x_531_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_box(1);
v___x_538_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4);
v___x_539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_537_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v_toCold_546_; lean_object* v_env_547_; lean_object* v_options_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_545_ = lean_st_ref_get(v___y_543_);
v_toCold_546_ = lean_ctor_get(v___y_542_, 0);
v_env_547_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_545_);
v_options_548_ = lean_ctor_get(v_toCold_546_, 2);
v___x_549_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2);
v___x_550_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_548_);
v___x_551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_551_, 0, v_env_547_);
lean_ctor_set(v___x_551_, 1, v___x_549_);
lean_ctor_set(v___x_551_, 2, v___x_550_);
lean_ctor_set(v___x_551_, 3, v_options_548_);
v___x_552_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_msgData_541_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object* v_msgData_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_554_, v___y_555_, v___y_556_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 2);
v___x_564_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msg_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_ref_563_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_ref_563_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_docComment_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_____x_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___x_592_; 
v___x_592_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_579_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_593_, v_a_580_, v_a_581_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
else
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_592_, 1);
v_____x_584_ = v_a_603_;
v___y_585_ = v_a_580_;
v___y_586_ = v_a_581_;
goto v___jp_583_;
}
v___jp_583_:
{
lean_object* v_snd_587_; lean_object* v_fst_588_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_591_; 
v_snd_587_ = lean_ctor_get(v_____x_584_, 1);
lean_inc(v_snd_587_);
v_fst_588_ = lean_ctor_get(v_____x_584_, 0);
lean_inc(v_fst_588_);
lean_dec_ref(v_____x_584_);
v_fst_589_ = lean_ctor_get(v_snd_587_, 0);
lean_inc(v_fst_589_);
v_snd_590_ = lean_ctor_get(v_snd_587_, 1);
lean_inc(v_snd_590_);
lean_dec(v_snd_587_);
v___x_591_ = l_Lean_parseVersoDocStringAt(v_fst_588_, v_fst_589_, v_snd_590_, v___y_585_, v___y_586_);
lean_dec(v_fst_588_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object* v_docComment_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_parseVersoDocString(v_docComment_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_docComment_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object* v_00_u03b1_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_610_, v___y_611_, v___y_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object* v_00_u03b1_615_, lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(v_00_u03b1_615_, v_msg_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_view_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_____x_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___x_651_; 
v___x_651_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_621_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_652_, v_a_622_, v_a_623_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_651_, 1);
v_____x_626_ = v_a_662_;
v___y_627_ = v_a_622_;
v___y_628_ = v_a_623_;
goto v___jp_625_;
}
v___jp_625_:
{
lean_object* v_snd_629_; lean_object* v_fst_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_snd_629_ = lean_ctor_get(v_____x_626_, 1);
lean_inc(v_snd_629_);
v_fst_630_ = lean_ctor_get(v_____x_626_, 0);
lean_inc(v_fst_630_);
lean_dec_ref(v_____x_626_);
v_fst_631_ = lean_ctor_get(v_snd_629_, 0);
lean_inc(v_fst_631_);
v_snd_632_ = lean_ctor_get(v_snd_629_, 1);
lean_inc(v_snd_632_);
lean_dec(v_snd_629_);
v___x_633_ = lean_box(0);
v___x_634_ = l_Lean_parseVersoDocStringAt(v_fst_630_, v_fst_631_, v_snd_632_, v___y_627_, v___y_628_);
lean_dec(v_fst_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; 
v_unused_642_ = lean_ctor_get(v___x_634_, 0);
lean_dec(v_unused_642_);
v___x_636_ = v___x_634_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_dec(v___x_634_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_633_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_633_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_634_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_view_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_reportVersoParseFailure(v_view_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec_ref(v_view_663_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_668_, lean_object* v_declName_669_, lean_object* v_binders_670_, lean_object* v___x_671_, uint8_t v___x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_668_) == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Doc_DocM_exec___redArg(v_declName_669_, v_binders_670_, v___x_671_, v___x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_680_;
}
else
{
lean_object* v_toCold_681_; lean_object* v_val_682_; lean_object* v_currRecDepth_683_; lean_object* v_ref_684_; uint8_t v_diag_685_; uint8_t v_suppressElabErrors_686_; lean_object* v_fileName_687_; lean_object* v_options_688_; lean_object* v_maxRecDepth_689_; lean_object* v_currNamespace_690_; lean_object* v_openDecls_691_; lean_object* v_initHeartbeats_692_; lean_object* v_maxHeartbeats_693_; lean_object* v_quotContext_694_; lean_object* v_currMacroScope_695_; lean_object* v_cancelTk_x3f_696_; lean_object* v_inheritedTraceOptions_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_toCold_681_ = lean_ctor_get(v___y_677_, 0);
v_val_682_ = lean_ctor_get(v_fileMap_x3f_668_, 0);
v_currRecDepth_683_ = lean_ctor_get(v___y_677_, 1);
v_ref_684_ = lean_ctor_get(v___y_677_, 2);
v_diag_685_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*3);
v_suppressElabErrors_686_ = lean_ctor_get_uint8(v___y_677_, sizeof(void*)*3 + 1);
v_fileName_687_ = lean_ctor_get(v_toCold_681_, 0);
v_options_688_ = lean_ctor_get(v_toCold_681_, 2);
v_maxRecDepth_689_ = lean_ctor_get(v_toCold_681_, 3);
v_currNamespace_690_ = lean_ctor_get(v_toCold_681_, 4);
v_openDecls_691_ = lean_ctor_get(v_toCold_681_, 5);
v_initHeartbeats_692_ = lean_ctor_get(v_toCold_681_, 6);
v_maxHeartbeats_693_ = lean_ctor_get(v_toCold_681_, 7);
v_quotContext_694_ = lean_ctor_get(v_toCold_681_, 8);
v_currMacroScope_695_ = lean_ctor_get(v_toCold_681_, 9);
v_cancelTk_x3f_696_ = lean_ctor_get(v_toCold_681_, 10);
v_inheritedTraceOptions_697_ = lean_ctor_get(v_toCold_681_, 11);
lean_inc_ref(v_inheritedTraceOptions_697_);
lean_inc(v_cancelTk_x3f_696_);
lean_inc(v_currMacroScope_695_);
lean_inc(v_quotContext_694_);
lean_inc(v_maxHeartbeats_693_);
lean_inc(v_initHeartbeats_692_);
lean_inc(v_openDecls_691_);
lean_inc(v_currNamespace_690_);
lean_inc(v_maxRecDepth_689_);
lean_inc_ref(v_options_688_);
lean_inc(v_val_682_);
lean_inc_ref(v_fileName_687_);
v___x_698_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_698_, 0, v_fileName_687_);
lean_ctor_set(v___x_698_, 1, v_val_682_);
lean_ctor_set(v___x_698_, 2, v_options_688_);
lean_ctor_set(v___x_698_, 3, v_maxRecDepth_689_);
lean_ctor_set(v___x_698_, 4, v_currNamespace_690_);
lean_ctor_set(v___x_698_, 5, v_openDecls_691_);
lean_ctor_set(v___x_698_, 6, v_initHeartbeats_692_);
lean_ctor_set(v___x_698_, 7, v_maxHeartbeats_693_);
lean_ctor_set(v___x_698_, 8, v_quotContext_694_);
lean_ctor_set(v___x_698_, 9, v_currMacroScope_695_);
lean_ctor_set(v___x_698_, 10, v_cancelTk_x3f_696_);
lean_ctor_set(v___x_698_, 11, v_inheritedTraceOptions_697_);
lean_inc(v_ref_684_);
lean_inc(v_currRecDepth_683_);
v___x_699_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_currRecDepth_683_);
lean_ctor_set(v___x_699_, 2, v_ref_684_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3, v_diag_685_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3 + 1, v_suppressElabErrors_686_);
v___x_700_ = l_Lean_Doc_DocM_exec___redArg(v_declName_669_, v_binders_670_, v___x_671_, v___x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___x_699_, v___y_678_);
lean_dec_ref_known(v___x_699_, 3);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_701_, lean_object* v_declName_702_, lean_object* v_binders_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___x_9808__boxed_713_; lean_object* v_res_714_; 
v___x_9808__boxed_713_ = lean_unbox(v___x_705_);
v_res_714_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_701_, v_declName_702_, v_binders_703_, v___x_704_, v___x_9808__boxed_713_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v_fileMap_x3f_701_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v___x_720_; lean_object* v_bs_x27_721_; size_t v___x_722_; size_t v___x_723_; lean_object* v___x_724_; 
v_v_719_ = lean_array_uget(v_bs_717_, v_i_716_);
v___x_720_ = lean_unsigned_to_nat(0u);
v_bs_x27_721_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_720_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_716_, v___x_722_);
v___x_724_ = lean_array_uset(v_bs_x27_721_, v_i_716_, v_v_719_);
v_i_716_ = v___x_723_;
v_bs_717_ = v___x_724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_726_, lean_object* v_i_727_, lean_object* v_bs_728_){
_start:
{
size_t v_sz_boxed_729_; size_t v_i_boxed_730_; lean_object* v_res_731_; 
v_sz_boxed_729_ = lean_unbox_usize(v_sz_726_);
lean_dec(v_sz_726_);
v_i_boxed_730_ = lean_unbox_usize(v_i_727_);
lean_dec(v_i_727_);
v_res_731_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_729_, v_i_boxed_730_, v_bs_728_);
return v_res_731_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_732_, lean_object* v_opt_733_){
_start:
{
lean_object* v_name_734_; lean_object* v_defValue_735_; lean_object* v_map_736_; lean_object* v___x_737_; 
v_name_734_ = lean_ctor_get(v_opt_733_, 0);
v_defValue_735_ = lean_ctor_get(v_opt_733_, 1);
v_map_736_ = lean_ctor_get(v_opts_732_, 0);
v___x_737_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_736_, v_name_734_);
if (lean_obj_tag(v___x_737_) == 0)
{
uint8_t v___x_738_; 
v___x_738_ = lean_unbox(v_defValue_735_);
return v___x_738_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v___x_737_, 1);
if (lean_obj_tag(v_val_739_) == 1)
{
uint8_t v_v_740_; 
v_v_740_ = lean_ctor_get_uint8(v_val_739_, 0);
lean_dec_ref_known(v_val_739_, 0);
return v_v_740_;
}
else
{
uint8_t v___x_741_; 
lean_dec(v_val_739_);
v___x_741_ = lean_unbox(v_defValue_735_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_742_, lean_object* v_opt_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_742_, v_opt_743_);
lean_dec_ref(v_opt_743_);
lean_dec_ref(v_opts_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_752_; lean_object* v_env_753_; lean_object* v___x_754_; lean_object* v_toCold_755_; lean_object* v_mctx_756_; lean_object* v_lctx_757_; lean_object* v_options_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_752_ = lean_st_ref_get(v___y_750_);
v_env_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc_ref(v_env_753_);
lean_dec(v___x_752_);
v___x_754_ = lean_st_ref_get(v___y_748_);
v_toCold_755_ = lean_ctor_get(v___y_749_, 0);
v_mctx_756_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_mctx_756_);
lean_dec(v___x_754_);
v_lctx_757_ = lean_ctor_get(v___y_747_, 2);
v_options_758_ = lean_ctor_get(v_toCold_755_, 2);
lean_inc_ref(v_options_758_);
lean_inc_ref(v_lctx_757_);
v___x_759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_759_, 0, v_env_753_);
lean_ctor_set(v___x_759_, 1, v_mctx_756_);
lean_ctor_set(v___x_759_, 2, v_lctx_757_);
lean_ctor_set(v___x_759_, 3, v_options_758_);
v___x_760_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
lean_ctor_set(v___x_760_, 1, v_msgData_746_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
return v_res_768_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_769_, uint8_t v___y_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_771_) == 1)
{
lean_object* v_pre_772_; 
v_pre_772_ = lean_ctor_get(v_x_771_, 0);
switch(lean_obj_tag(v_pre_772_))
{
case 1:
{
lean_object* v_pre_773_; 
v_pre_773_ = lean_ctor_get(v_pre_772_, 0);
switch(lean_obj_tag(v_pre_773_))
{
case 0:
{
lean_object* v_str_774_; lean_object* v_str_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_str_774_ = lean_ctor_get(v_x_771_, 1);
v_str_775_ = lean_ctor_get(v_pre_772_, 1);
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_777_ = lean_string_dec_eq(v_str_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_779_ = lean_string_dec_eq(v_str_775_, v___x_778_);
if (v___x_779_ == 0)
{
return v___x_779_;
}
else
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_781_ = lean_string_dec_eq(v_str_774_, v___x_780_);
if (v___x_781_ == 0)
{
return v___x_781_;
}
else
{
return v_suppressElabErrors_769_;
}
}
}
else
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_783_ = lean_string_dec_eq(v_str_774_, v___x_782_);
if (v___x_783_ == 0)
{
return v___x_783_;
}
else
{
return v_suppressElabErrors_769_;
}
}
}
case 1:
{
lean_object* v_pre_784_; 
v_pre_784_ = lean_ctor_get(v_pre_773_, 0);
if (lean_obj_tag(v_pre_784_) == 0)
{
lean_object* v_str_785_; lean_object* v_str_786_; lean_object* v_str_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_str_785_ = lean_ctor_get(v_x_771_, 1);
v_str_786_ = lean_ctor_get(v_pre_772_, 1);
v_str_787_ = lean_ctor_get(v_pre_773_, 1);
v___x_788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_789_ = lean_string_dec_eq(v_str_787_, v___x_788_);
if (v___x_789_ == 0)
{
return v___x_789_;
}
else
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_791_ = lean_string_dec_eq(v_str_786_, v___x_790_);
if (v___x_791_ == 0)
{
return v___x_791_;
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_793_ = lean_string_dec_eq(v_str_785_, v___x_792_);
if (v___x_793_ == 0)
{
return v___x_793_;
}
else
{
return v_suppressElabErrors_769_;
}
}
}
}
else
{
return v___y_770_;
}
}
default: 
{
return v___y_770_;
}
}
}
case 0:
{
lean_object* v_str_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_str_794_ = lean_ctor_get(v_x_771_, 1);
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_796_ = lean_string_dec_eq(v_str_794_, v___x_795_);
if (v___x_796_ == 0)
{
return v___x_796_;
}
else
{
return v_suppressElabErrors_769_;
}
}
default: 
{
return v___y_770_;
}
}
}
else
{
return v___y_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_797_, lean_object* v___y_798_, lean_object* v_x_799_){
_start:
{
uint8_t v_suppressElabErrors_boxed_800_; uint8_t v___y_9899__boxed_801_; uint8_t v_res_802_; lean_object* v_r_803_; 
v_suppressElabErrors_boxed_800_ = lean_unbox(v_suppressElabErrors_797_);
v___y_9899__boxed_801_ = lean_unbox(v___y_798_);
v_res_802_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_800_, v___y_9899__boxed_801_, v_x_799_);
lean_dec(v_x_799_);
v_r_803_ = lean_box(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_804_, lean_object* v_msgData_805_, uint8_t v_severity_806_, uint8_t v_isSilent_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
uint8_t v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; uint8_t v___y_820_; lean_object* v_currNamespace_821_; lean_object* v_openDecls_822_; lean_object* v___y_823_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; uint8_t v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; uint8_t v___y_856_; uint8_t v___y_857_; lean_object* v___y_858_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; uint8_t v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; uint8_t v___y_883_; uint8_t v___y_884_; lean_object* v___y_885_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; uint8_t v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___x_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___y_909_; uint8_t v___y_910_; lean_object* v___y_911_; uint8_t v___y_912_; uint8_t v___y_914_; uint8_t v___x_932_; 
v___x_902_ = 2;
v___x_932_ = l_Lean_instBEqMessageSeverity_beq(v_severity_806_, v___x_902_);
if (v___x_932_ == 0)
{
v___y_914_ = v___x_932_;
goto v___jp_913_;
}
else
{
uint8_t v___x_933_; 
lean_inc_ref(v_msgData_805_);
v___x_933_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_805_);
v___y_914_ = v___x_933_;
goto v___jp_913_;
}
v___jp_813_:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_env_828_; lean_object* v_nextMacroScope_829_; lean_object* v_ngen_830_; lean_object* v_auxDeclNGen_831_; lean_object* v_traceState_832_; lean_object* v_cache_833_; lean_object* v_messages_834_; lean_object* v_infoState_835_; lean_object* v_snapshotTasks_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_847_; 
lean_inc(v_openDecls_822_);
lean_inc(v_currNamespace_821_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_currNamespace_821_);
lean_ctor_set(v___x_824_, 1, v_openDecls_822_);
v___x_825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v___y_815_);
lean_inc_ref(v___y_819_);
lean_inc_ref(v___y_818_);
v___x_826_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_826_, 0, v___y_818_);
lean_ctor_set(v___x_826_, 1, v___y_817_);
lean_ctor_set(v___x_826_, 2, v___y_816_);
lean_ctor_set(v___x_826_, 3, v___y_819_);
lean_ctor_set(v___x_826_, 4, v___x_825_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*5, v___y_820_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*5 + 1, v___y_814_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*5 + 2, v_isSilent_807_);
v___x_827_ = lean_st_ref_take(v___y_823_);
v_env_828_ = lean_ctor_get(v___x_827_, 0);
v_nextMacroScope_829_ = lean_ctor_get(v___x_827_, 1);
v_ngen_830_ = lean_ctor_get(v___x_827_, 2);
v_auxDeclNGen_831_ = lean_ctor_get(v___x_827_, 3);
v_traceState_832_ = lean_ctor_get(v___x_827_, 4);
v_cache_833_ = lean_ctor_get(v___x_827_, 5);
v_messages_834_ = lean_ctor_get(v___x_827_, 6);
v_infoState_835_ = lean_ctor_get(v___x_827_, 7);
v_snapshotTasks_836_ = lean_ctor_get(v___x_827_, 8);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_847_ == 0)
{
v___x_838_ = v___x_827_;
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snapshotTasks_836_);
lean_inc(v_infoState_835_);
lean_inc(v_messages_834_);
lean_inc(v_cache_833_);
lean_inc(v_traceState_832_);
lean_inc(v_auxDeclNGen_831_);
lean_inc(v_ngen_830_);
lean_inc(v_nextMacroScope_829_);
lean_inc(v_env_828_);
lean_dec(v___x_827_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_847_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_box(0);
v___x_841_ = l_Lean_MessageLog_add(v___x_826_, v_messages_834_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 6, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_env_828_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_nextMacroScope_829_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_ngen_830_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_auxDeclNGen_831_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v_traceState_832_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_cache_833_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_infoState_835_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v_snapshotTasks_836_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_st_ref_put(v___y_823_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_840_);
return v___x_845_;
}
}
}
v___jp_848_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_874_; 
v___x_859_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_805_);
v___x_860_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_859_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_874_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_inc_ref_n(v___y_855_, 2);
v___x_865_ = l_Lean_FileMap_toPosition(v___y_855_, v___y_853_);
lean_dec(v___y_853_);
v___x_866_ = l_Lean_FileMap_toPosition(v___y_855_, v___y_858_);
lean_dec(v___y_858_);
v___x_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
v___x_868_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_856_ == 0)
{
lean_del_object(v___x_863_);
lean_dec_ref(v___y_850_);
v___y_814_ = v___y_852_;
v___y_815_ = v_a_861_;
v___y_816_ = v___x_867_;
v___y_817_ = v___x_865_;
v___y_818_ = v___y_854_;
v___y_819_ = v___x_868_;
v___y_820_ = v___y_857_;
v_currNamespace_821_ = v___y_851_;
v_openDecls_822_ = v___y_849_;
v___y_823_ = v___y_811_;
goto v___jp_813_;
}
else
{
uint8_t v___x_869_; 
lean_inc(v_a_861_);
v___x_869_ = l_Lean_MessageData_hasTag(v___y_850_, v_a_861_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec_ref_known(v___x_867_, 1);
lean_dec_ref(v___x_865_);
lean_dec(v_a_861_);
v___x_870_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_870_);
v___x_872_ = v___x_863_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
else
{
lean_del_object(v___x_863_);
v___y_814_ = v___y_852_;
v___y_815_ = v_a_861_;
v___y_816_ = v___x_867_;
v___y_817_ = v___x_865_;
v___y_818_ = v___y_854_;
v___y_819_ = v___x_868_;
v___y_820_ = v___y_857_;
v_currNamespace_821_ = v___y_851_;
v_openDecls_822_ = v___y_849_;
v___y_823_ = v___y_811_;
goto v___jp_813_;
}
}
}
}
v___jp_875_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Syntax_getTailPos_x3f(v___y_880_, v___y_884_);
lean_dec(v___y_880_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_inc(v___y_885_);
v___y_849_ = v___y_876_;
v___y_850_ = v___y_877_;
v___y_851_ = v___y_878_;
v___y_852_ = v___y_879_;
v___y_853_ = v___y_885_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_882_;
v___y_856_ = v___y_883_;
v___y_857_ = v___y_884_;
v___y_858_ = v___y_885_;
goto v___jp_848_;
}
else
{
lean_object* v_val_887_; 
v_val_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v___x_886_, 1);
v___y_849_ = v___y_876_;
v___y_850_ = v___y_877_;
v___y_851_ = v___y_878_;
v___y_852_ = v___y_879_;
v___y_853_ = v___y_885_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_882_;
v___y_856_ = v___y_883_;
v___y_857_ = v___y_884_;
v___y_858_ = v_val_887_;
goto v___jp_848_;
}
}
v___jp_888_:
{
lean_object* v_ref_898_; lean_object* v___x_899_; 
v_ref_898_ = l_Lean_replaceRef(v_ref_804_, v___y_896_);
v___x_899_ = l_Lean_Syntax_getPos_x3f(v_ref_898_, v___y_895_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___y_876_ = v___y_889_;
v___y_877_ = v___y_890_;
v___y_878_ = v___y_891_;
v___y_879_ = v___y_897_;
v___y_880_ = v_ref_898_;
v___y_881_ = v___y_892_;
v___y_882_ = v___y_893_;
v___y_883_ = v___y_894_;
v___y_884_ = v___y_895_;
v___y_885_ = v___x_900_;
goto v___jp_875_;
}
else
{
lean_object* v_val_901_; 
v_val_901_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v___x_899_, 1);
v___y_876_ = v___y_889_;
v___y_877_ = v___y_890_;
v___y_878_ = v___y_891_;
v___y_879_ = v___y_897_;
v___y_880_ = v_ref_898_;
v___y_881_ = v___y_892_;
v___y_882_ = v___y_893_;
v___y_883_ = v___y_894_;
v___y_884_ = v___y_895_;
v___y_885_ = v_val_901_;
goto v___jp_875_;
}
}
v___jp_903_:
{
if (v___y_912_ == 0)
{
v___y_889_ = v___y_904_;
v___y_890_ = v___y_906_;
v___y_891_ = v___y_908_;
v___y_892_ = v___y_905_;
v___y_893_ = v___y_907_;
v___y_894_ = v___y_909_;
v___y_895_ = v___y_910_;
v___y_896_ = v___y_911_;
v___y_897_ = v_severity_806_;
goto v___jp_888_;
}
else
{
v___y_889_ = v___y_904_;
v___y_890_ = v___y_906_;
v___y_891_ = v___y_908_;
v___y_892_ = v___y_905_;
v___y_893_ = v___y_907_;
v___y_894_ = v___y_909_;
v___y_895_ = v___y_910_;
v___y_896_ = v___y_911_;
v___y_897_ = v___x_902_;
goto v___jp_888_;
}
}
v___jp_913_:
{
if (v___y_914_ == 0)
{
lean_object* v_toCold_915_; lean_object* v_ref_916_; uint8_t v_suppressElabErrors_917_; lean_object* v_fileName_918_; lean_object* v_fileMap_919_; lean_object* v_options_920_; lean_object* v_currNamespace_921_; lean_object* v_openDecls_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; uint8_t v___x_926_; uint8_t v___x_927_; 
v_toCold_915_ = lean_ctor_get(v___y_810_, 0);
v_ref_916_ = lean_ctor_get(v___y_810_, 2);
v_suppressElabErrors_917_ = lean_ctor_get_uint8(v___y_810_, sizeof(void*)*3 + 1);
v_fileName_918_ = lean_ctor_get(v_toCold_915_, 0);
v_fileMap_919_ = lean_ctor_get(v_toCold_915_, 1);
v_options_920_ = lean_ctor_get(v_toCold_915_, 2);
v_currNamespace_921_ = lean_ctor_get(v_toCold_915_, 4);
v_openDecls_922_ = lean_ctor_get(v_toCold_915_, 5);
v___x_923_ = lean_box(v_suppressElabErrors_917_);
v___x_924_ = lean_box(v___y_914_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_925_, 0, v___x_923_);
lean_closure_set(v___f_925_, 1, v___x_924_);
v___x_926_ = 1;
v___x_927_ = l_Lean_instBEqMessageSeverity_beq(v_severity_806_, v___x_926_);
if (v___x_927_ == 0)
{
v___y_904_ = v_openDecls_922_;
v___y_905_ = v_fileName_918_;
v___y_906_ = v___f_925_;
v___y_907_ = v_fileMap_919_;
v___y_908_ = v_currNamespace_921_;
v___y_909_ = v_suppressElabErrors_917_;
v___y_910_ = v___y_914_;
v___y_911_ = v_ref_916_;
v___y_912_ = v___x_927_;
goto v___jp_903_;
}
else
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = l_Lean_warningAsError;
v___x_929_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_920_, v___x_928_);
v___y_904_ = v_openDecls_922_;
v___y_905_ = v_fileName_918_;
v___y_906_ = v___f_925_;
v___y_907_ = v_fileMap_919_;
v___y_908_ = v_currNamespace_921_;
v___y_909_ = v_suppressElabErrors_917_;
v___y_910_ = v___y_914_;
v___y_911_ = v_ref_916_;
v___y_912_ = v___x_929_;
goto v___jp_903_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_msgData_805_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_934_, lean_object* v_msgData_935_, lean_object* v_severity_936_, lean_object* v_isSilent_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_severity_boxed_943_; uint8_t v_isSilent_boxed_944_; lean_object* v_res_945_; 
v_severity_boxed_943_ = lean_unbox(v_severity_936_);
v_isSilent_boxed_944_ = lean_unbox(v_isSilent_937_);
v_res_945_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_934_, v_msgData_935_, v_severity_boxed_943_, v_isSilent_boxed_944_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v_ref_934_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_b_949_);
return v___x_958_;
}
else
{
lean_object* v_ref_959_; lean_object* v_a_960_; uint8_t v_severity_961_; uint8_t v_isSilent_962_; lean_object* v_data_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_ref_959_ = lean_ctor_get(v___y_954_, 2);
v_a_960_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
v_severity_961_ = lean_ctor_get_uint8(v_a_960_, sizeof(void*)*5 + 1);
v_isSilent_962_ = lean_ctor_get_uint8(v_a_960_, sizeof(void*)*5 + 2);
v_data_963_ = lean_ctor_get(v_a_960_, 4);
v___x_964_ = lean_box(0);
lean_inc(v_data_963_);
v___x_965_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_959_, v_data_963_, v_severity_961_, v_isSilent_962_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
if (lean_obj_tag(v___x_965_) == 0)
{
size_t v___x_966_; size_t v___x_967_; 
lean_dec_ref_known(v___x_965_, 1);
v___x_966_ = ((size_t)1ULL);
v___x_967_ = lean_usize_add(v_i_948_, v___x_966_);
v_i_948_ = v___x_967_;
v_b_949_ = v___x_964_;
goto _start;
}
else
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_969_, lean_object* v_sz_970_, lean_object* v_i_971_, lean_object* v_b_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
size_t v_sz_boxed_980_; size_t v_i_boxed_981_; lean_object* v_res_982_; 
v_sz_boxed_980_ = lean_unbox_usize(v_sz_970_);
lean_dec(v_sz_970_);
v_i_boxed_981_ = lean_unbox_usize(v_i_971_);
lean_dec(v_i_971_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_969_, v_sz_boxed_980_, v_i_boxed_981_, v_b_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_as_969_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_infoState_987_; lean_object* v_env_988_; lean_object* v_nextMacroScope_989_; lean_object* v_ngen_990_; lean_object* v_auxDeclNGen_991_; lean_object* v_traceState_992_; lean_object* v_cache_993_; lean_object* v_messages_994_; lean_object* v_snapshotTasks_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1015_; 
v___x_986_ = lean_st_ref_take(v___y_984_);
v_infoState_987_ = lean_ctor_get(v___x_986_, 7);
v_env_988_ = lean_ctor_get(v___x_986_, 0);
v_nextMacroScope_989_ = lean_ctor_get(v___x_986_, 1);
v_ngen_990_ = lean_ctor_get(v___x_986_, 2);
v_auxDeclNGen_991_ = lean_ctor_get(v___x_986_, 3);
v_traceState_992_ = lean_ctor_get(v___x_986_, 4);
v_cache_993_ = lean_ctor_get(v___x_986_, 5);
v_messages_994_ = lean_ctor_get(v___x_986_, 6);
v_snapshotTasks_995_ = lean_ctor_get(v___x_986_, 8);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_997_ = v___x_986_;
v_isShared_998_ = v_isSharedCheck_1015_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snapshotTasks_995_);
lean_inc(v_infoState_987_);
lean_inc(v_messages_994_);
lean_inc(v_cache_993_);
lean_inc(v_traceState_992_);
lean_inc(v_auxDeclNGen_991_);
lean_inc(v_ngen_990_);
lean_inc(v_nextMacroScope_989_);
lean_inc(v_env_988_);
lean_dec(v___x_986_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1015_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_assignment_999_; lean_object* v_lazyAssignment_1000_; lean_object* v_trees_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1014_; 
v_assignment_999_ = lean_ctor_get(v_infoState_987_, 0);
v_lazyAssignment_1000_ = lean_ctor_get(v_infoState_987_, 1);
v_trees_1001_ = lean_ctor_get(v_infoState_987_, 2);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_infoState_987_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1003_ = v_infoState_987_;
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_trees_1001_);
lean_inc(v_lazyAssignment_1000_);
lean_inc(v_assignment_999_);
lean_dec(v_infoState_987_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_assignment_999_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_lazyAssignment_1000_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_trees_1001_);
v___x_1007_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*3, v_flag_983_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 7, v___x_1007_);
v___x_1009_ = v___x_997_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_env_988_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v_nextMacroScope_989_);
lean_ctor_set(v_reuseFailAlloc_1012_, 2, v_ngen_990_);
lean_ctor_set(v_reuseFailAlloc_1012_, 3, v_auxDeclNGen_991_);
lean_ctor_set(v_reuseFailAlloc_1012_, 4, v_traceState_992_);
lean_ctor_set(v_reuseFailAlloc_1012_, 5, v_cache_993_);
lean_ctor_set(v_reuseFailAlloc_1012_, 6, v_messages_994_);
lean_ctor_set(v_reuseFailAlloc_1012_, 7, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1012_, 8, v_snapshotTasks_995_);
v___x_1009_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_st_ref_put(v___y_984_, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1005_);
return v___x_1011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
uint8_t v_flag_boxed_1019_; lean_object* v_res_1020_; 
v_flag_boxed_1019_ = lean_unbox(v_flag_1016_);
v_res_1020_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1019_, v___y_1017_);
lean_dec(v___y_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_infoState_1031_; uint8_t v_enabled_1032_; lean_object* v_a_1034_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1030_ = lean_st_ref_get(v___y_1028_);
v_infoState_1031_ = lean_ctor_get(v___x_1030_, 7);
lean_inc_ref(v_infoState_1031_);
lean_dec(v___x_1030_);
v_enabled_1032_ = lean_ctor_get_uint8(v_infoState_1031_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1031_);
v___x_1044_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1021_, v___y_1028_);
lean_dec_ref(v___x_1044_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
lean_inc(v___y_1026_);
lean_inc_ref(v___y_1025_);
lean_inc(v___y_1024_);
lean_inc_ref(v___y_1023_);
v___x_1045_ = lean_apply_7(v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, lean_box(0));
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1032_, v___y_1028_);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1047_, 0);
lean_dec(v_unused_1055_);
v___x_1049_ = v___x_1047_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v___x_1047_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v_a_1046_);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1046_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v_a_1056_; 
v_a_1056_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1056_);
lean_dec_ref_known(v___x_1045_, 1);
v_a_1034_ = v_a_1056_;
goto v___jp_1033_;
}
v___jp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v___x_1035_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1032_, v___y_1028_);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1043_);
v___x_1037_ = v___x_1035_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1035_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 0, v_a_1034_);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1057_, lean_object* v_x_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v_flag_boxed_1066_; lean_object* v_res_1067_; 
v_flag_boxed_1066_ = lean_unbox(v_flag_1057_);
v_res_1067_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1066_, v_x_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1068_, lean_object* v_binders_1069_, lean_object* v_blocks_1070_, lean_object* v_fileMap_x3f_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v_a_1082_; size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_sz_1100_ = lean_array_size(v_blocks_1070_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1100_, v___x_1101_, v_blocks_1070_);
v___x_1103_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = 1;
v___x_1105_ = lean_box(v___x_1104_);
v___y_1106_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1106_, 0, v_fileMap_x3f_1071_);
lean_closure_set(v___y_1106_, 1, v_declName_1068_);
lean_closure_set(v___y_1106_, 2, v_binders_1069_);
lean_closure_set(v___y_1106_, 3, v___x_1103_);
lean_closure_set(v___y_1106_, 4, v___x_1105_);
v___x_1107_ = 0;
v___x_1108_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1107_, v___y_1106_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1077_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = l_Lean_Core_setMessageLog___redArg(v_a_1080_, v_a_1077_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; lean_object* v___x_1116_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1113_ = l_Lean_MessageLog_toArray(v_a_1111_);
lean_dec(v_a_1111_);
v___x_1114_ = lean_box(0);
v_sz_1115_ = lean_array_size(v___x_1113_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1113_, v_sz_1115_, v___x_1101_, v___x_1114_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v___x_1113_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1141_; 
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v___x_1116_, 0);
lean_dec(v_unused_1142_);
v___x_1118_ = v___x_1116_;
v_isShared_1119_ = v_isSharedCheck_1141_;
goto v_resetjp_1117_;
}
else
{
lean_dec(v___x_1116_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1141_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_fst_1120_; lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1140_; 
v_fst_1120_ = lean_ctor_get(v_a_1109_, 0);
v_snd_1121_ = lean_ctor_get(v_a_1109_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_a_1109_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1123_ = v_a_1109_;
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_inc(v_fst_1120_);
lean_dec(v_a_1109_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1140_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1139_; 
v_fst_1125_ = lean_ctor_get(v_fst_1120_, 0);
v_snd_1126_ = lean_ctor_get(v_fst_1120_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_fst_1120_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1128_ = v_fst_1120_;
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_snd_1126_);
lean_inc(v_fst_1125_);
lean_dec(v_fst_1120_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1139_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_fst_1125_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_snd_1126_);
v___x_1131_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1131_);
v___x_1133_ = v___x_1123_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_snd_1121_);
v___x_1133_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1135_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1133_);
v___x_1135_ = v___x_1118_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_a_1109_);
v_a_1143_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1116_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1116_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1111_);
lean_dec(v_a_1109_);
v_a_1151_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1112_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1112_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; 
lean_dec(v_a_1109_);
v_a_1159_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1110_, 1);
v_a_1082_ = v_a_1159_;
goto v___jp_1081_;
}
}
else
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1108_, 1);
v_a_1082_ = v_a_1160_;
goto v___jp_1081_;
}
v___jp_1081_:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Core_setMessageLog___redArg(v_a_1080_, v_a_1077_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v___x_1083_, 0);
lean_dec(v_unused_1091_);
v___x_1085_ = v___x_1083_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v___x_1083_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 1);
lean_ctor_set(v___x_1085_, 0, v_a_1082_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1082_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref(v_a_1082_);
v_a_1092_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1083_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1083_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec(v_fileMap_x3f_1071_);
lean_dec_ref(v_blocks_1070_);
lean_dec(v_binders_1069_);
lean_dec(v_declName_1068_);
v_a_1161_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1079_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1079_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1169_, lean_object* v_binders_1170_, lean_object* v_blocks_1171_, lean_object* v_fileMap_x3f_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1169_, v_binders_1170_, v_blocks_1171_, v_fileMap_x3f_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1181_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
uint8_t v_flag_boxed_1198_; lean_object* v_res_1199_; 
v_flag_boxed_1198_ = lean_unbox(v_flag_1190_);
v_res_1199_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1198_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1200_, uint8_t v_flag_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1201_, v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1211_, lean_object* v_flag_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_flag_boxed_1221_; lean_object* v_res_1222_; 
v_flag_boxed_1221_ = lean_unbox(v_flag_1212_);
v_res_1222_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1211_, v_flag_boxed_1221_, v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1223_, lean_object* v_msgData_1224_, uint8_t v_severity_1225_, uint8_t v_isSilent_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1223_, v_msgData_1224_, v_severity_1225_, v_isSilent_1226_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1235_, lean_object* v_msgData_1236_, lean_object* v_severity_1237_, lean_object* v_isSilent_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
uint8_t v_severity_boxed_1246_; uint8_t v_isSilent_boxed_1247_; lean_object* v_res_1248_; 
v_severity_boxed_1246_ = lean_unbox(v_severity_1237_);
v_isSilent_boxed_1247_ = lean_unbox(v_isSilent_1238_);
v_res_1248_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1235_, v_msgData_1236_, v_severity_boxed_1246_, v_isSilent_boxed_1247_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v_ref_1235_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1249_, uint8_t v_severity_1250_, uint8_t v_isSilent_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_ref_1257_; lean_object* v___x_1258_; 
v_ref_1257_ = lean_ctor_get(v___y_1254_, 2);
v___x_1258_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1257_, v_msgData_1249_, v_severity_1250_, v_isSilent_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1259_, lean_object* v_severity_1260_, lean_object* v_isSilent_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v_severity_boxed_1267_; uint8_t v_isSilent_boxed_1268_; lean_object* v_res_1269_; 
v_severity_boxed_1267_ = lean_unbox(v_severity_1260_);
v_isSilent_boxed_1268_ = lean_unbox(v_isSilent_1261_);
v_res_1269_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1259_, v_severity_boxed_1267_, v_isSilent_boxed_1268_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_1278_; uint8_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = 2;
v___x_1279_ = 0;
v___x_1280_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1270_, v___x_1278_, v___x_1279_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1290_, size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_b_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v___x_1301_; 
v___x_1301_ = lean_usize_dec_lt(v_i_1292_, v_sz_1291_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_b_1293_);
return v___x_1302_;
}
else
{
lean_object* v_a_1303_; lean_object* v_snd_1304_; lean_object* v_snd_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_a_1303_ = lean_array_uget_borrowed(v_as_1290_, v_i_1292_);
v_snd_1304_ = lean_ctor_get(v_a_1303_, 1);
v_snd_1305_ = lean_ctor_get(v_snd_1304_, 1);
v___x_1306_ = lean_box(0);
lean_inc(v_snd_1305_);
v___x_1307_ = l_Lean_Parser_Error_toString(v_snd_1305_);
v___x_1308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
v___x_1310_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1309_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
if (lean_obj_tag(v___x_1310_) == 0)
{
size_t v___x_1311_; size_t v___x_1312_; 
lean_dec_ref_known(v___x_1310_, 1);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1292_, v___x_1311_);
v_i_1292_ = v___x_1312_;
v_b_1293_ = v___x_1306_;
goto _start;
}
else
{
return v___x_1310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1314_, lean_object* v_sz_1315_, lean_object* v_i_1316_, lean_object* v_b_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
size_t v_sz_boxed_1325_; size_t v_i_boxed_1326_; lean_object* v_res_1327_; 
v_sz_boxed_1325_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v_i_boxed_1326_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_res_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1314_, v_sz_boxed_1325_, v_i_boxed_1326_, v_b_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec_ref(v_as_1314_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1346_, lean_object* v_binders_1347_, lean_object* v_docComment_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_toCold_1357_; lean_object* v_env_1358_; lean_object* v_fileName_1359_; lean_object* v_options_1360_; lean_object* v_currNamespace_1361_; lean_object* v_openDecls_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1356_ = lean_st_ref_get(v_a_1354_);
v_toCold_1357_ = lean_ctor_get(v_a_1353_, 0);
v_env_1358_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_ref_n(v_env_1358_, 2);
lean_dec(v___x_1356_);
v_fileName_1359_ = lean_ctor_get(v_toCold_1357_, 0);
v_options_1360_ = lean_ctor_get(v_toCold_1357_, 2);
v_currNamespace_1361_ = lean_ctor_get(v_toCold_1357_, 4);
v_openDecls_1362_ = lean_ctor_get(v_toCold_1357_, 5);
v___x_1363_ = lean_string_utf8_byte_size(v_docComment_1348_);
lean_inc_ref_n(v_docComment_1348_, 2);
v___x_1364_ = l_Lean_FileMap_ofString(v_docComment_1348_);
lean_inc_ref(v___x_1364_);
lean_inc_ref(v_fileName_1359_);
v___x_1365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1365_, 0, v_docComment_1348_);
lean_ctor_set(v___x_1365_, 1, v_fileName_1359_);
lean_ctor_set(v___x_1365_, 2, v___x_1364_);
lean_ctor_set(v___x_1365_, 3, v___x_1363_);
lean_inc(v_openDecls_1362_);
lean_inc(v_currNamespace_1361_);
lean_inc_ref(v_options_1360_);
v___x_1366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1366_, 0, v_env_1358_);
lean_ctor_set(v___x_1366_, 1, v_options_1360_);
lean_ctor_set(v___x_1366_, 2, v_currNamespace_1361_);
lean_ctor_set(v___x_1366_, 3, v_openDecls_1362_);
v___x_1367_ = l_Lean_Parser_mkParserState(v_docComment_1348_);
lean_dec_ref(v_docComment_1348_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1370_ = l_Lean_Parser_getTokenTable(v_env_1358_);
v___x_1371_ = l_Lean_Parser_ParserFn_run(v___x_1369_, v___x_1365_, v___x_1366_, v___x_1370_, v___x_1367_);
lean_inc_ref(v___x_1371_);
v___x_1372_ = l_Lean_Parser_ParserState_allErrors(v___x_1371_);
v___x_1373_ = lean_array_get_size(v___x_1372_);
v___x_1374_ = lean_nat_dec_eq(v___x_1373_, v___x_1368_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; size_t v_sz_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v___x_1371_);
lean_dec_ref(v___x_1364_);
lean_dec(v_binders_1347_);
lean_dec(v_declName_1346_);
v___x_1375_ = lean_box(0);
v_sz_1376_ = lean_array_size(v___x_1372_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1372_, v_sz_1376_, v___x_1377_, v___x_1375_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec_ref(v___x_1372_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1386_; 
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1378_, 0);
lean_dec(v_unused_1387_);
v___x_1380_ = v___x_1378_;
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v___x_1378_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1386_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1382_);
v___x_1384_ = v___x_1380_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1378_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1378_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_stxStack_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___x_1372_);
v_stxStack_1396_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref(v_stxStack_1396_);
lean_dec_ref(v___x_1371_);
v___x_1397_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1396_);
lean_dec_ref(v_stxStack_1396_);
v___x_1398_ = l_Lean_TSyntax_getVersoBlocks(v___x_1397_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1364_);
v___x_1400_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1346_, v_binders_1347_, v___x_1398_, v___x_1399_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1401_, lean_object* v_binders_1402_, lean_object* v_docComment_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_versoDocStringOfText(v_declName_1401_, v_binders_1402_, v_docComment_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1412_, uint8_t v_severity_1413_, uint8_t v_isSilent_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1412_, v_severity_1413_, v_isSilent_1414_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1423_, lean_object* v_severity_1424_, lean_object* v_isSilent_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_severity_boxed_1433_; uint8_t v_isSilent_boxed_1434_; lean_object* v_res_1435_; 
v_severity_boxed_1433_ = lean_unbox(v_severity_1424_);
v_isSilent_boxed_1434_ = lean_unbox(v_isSilent_1425_);
v_res_1435_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1423_, v_severity_boxed_1433_, v_isSilent_boxed_1434_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1445_, lean_object* v_binders_1446_, lean_object* v_docComment_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1447_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v___x_1456_; lean_object* v_body_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
lean_dec_ref_known(v___x_1455_, 1);
v___x_1456_ = lean_unsigned_to_nat(1u);
v_body_1457_ = l_Lean_Syntax_getArg(v_docComment_1447_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1459_ = l_Lean_Syntax_isOfKind(v_body_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = l_Lean_TSyntax_getDocString(v_docComment_1447_);
v___x_1461_ = l_Lean_versoDocStringOfText(v_declName_1445_, v_binders_1446_, v___x_1460_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v_markup_1463_; 
v___x_1462_ = l_Lean_VersoDocstringView_of(v_docComment_1447_);
v_markup_1463_ = lean_ctor_get(v___x_1462_, 1);
lean_inc_ref(v_markup_1463_);
lean_dec_ref(v___x_1462_);
if (lean_obj_tag(v_markup_1463_) == 0)
{
lean_object* v_doc_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v_doc_1464_ = lean_ctor_get(v_markup_1463_, 0);
lean_inc(v_doc_1464_);
lean_dec_ref_known(v_markup_1463_, 1);
v___x_1465_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1464_);
lean_dec(v_doc_1464_);
v___x_1466_ = lean_box(0);
v___x_1467_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1445_, v_binders_1446_, v___x_1465_, v___x_1466_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1467_;
}
else
{
lean_object* v_text_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_text_1468_ = lean_ctor_get(v_markup_1463_, 0);
lean_inc(v_text_1468_);
lean_dec_ref_known(v_markup_1463_, 1);
v___x_1469_ = l_Lean_Syntax_getAtomVal(v_text_1468_);
lean_dec(v_text_1468_);
v___x_1470_ = l_Lean_versoDocStringOfText(v_declName_1445_, v_binders_1446_, v___x_1469_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1470_;
}
}
}
else
{
lean_object* v___x_1471_; 
lean_dec_ref_known(v___x_1455_, 1);
v___x_1471_ = l_Lean_parseVersoDocString(v_docComment_1447_, v_a_1452_, v_a_1453_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1519_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1519_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1519_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
if (lean_obj_tag(v_a_1472_) == 1)
{
lean_object* v_val_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; 
lean_del_object(v___x_1474_);
v_val_1476_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_val_1476_);
lean_dec_ref_known(v_a_1472_, 1);
v___x_1477_ = l_Lean_TSyntax_getVersoBlocks(v_val_1476_);
lean_dec(v_val_1476_);
v___x_1478_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1478_, 0, v___x_1477_);
v___x_1479_ = 0;
v___x_1480_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1445_, v_binders_1446_, v___x_1478_, v___x_1479_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1506_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1505_; 
v_fst_1485_ = lean_ctor_get(v_a_1481_, 0);
v_snd_1486_ = lean_ctor_get(v_a_1481_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_a_1481_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1488_ = v_a_1481_;
v_isShared_1489_ = v_isSharedCheck_1505_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snd_1486_);
lean_inc(v_fst_1485_);
lean_dec(v_a_1481_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1505_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1504_; 
v_fst_1490_ = lean_ctor_get(v_fst_1485_, 0);
v_snd_1491_ = lean_ctor_get(v_fst_1485_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_fst_1485_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1493_ = v_fst_1485_;
v_isShared_1494_ = v_isSharedCheck_1504_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_snd_1491_);
lean_inc(v_fst_1490_);
lean_dec(v_fst_1485_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1504_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_fst_1490_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_snd_1491_);
v___x_1496_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1496_);
v___x_1498_ = v___x_1488_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_snd_1486_);
v___x_1498_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1498_);
v___x_1500_ = v___x_1483_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_a_1507_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1480_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1480_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1517_; 
lean_dec(v_a_1472_);
lean_dec(v_binders_1446_);
lean_dec(v_declName_1445_);
v___x_1515_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1515_);
v___x_1517_ = v___x_1474_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_binders_1446_);
lean_dec(v_declName_1445_);
v_a_1520_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1471_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1471_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1528_, lean_object* v_binders_1529_, lean_object* v_docComment_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_versoDocString(v_declName_1528_, v_binders_1529_, v_docComment_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_docComment_1530_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1539_, lean_object* v_doc_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_val_1556_; lean_object* v_env_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1548_ = lean_st_ref_get(v_a_1546_);
v_env_1558_ = lean_ctor_get(v___x_1548_, 0);
lean_inc_ref(v_env_1558_);
lean_dec(v___x_1548_);
v___x_1559_ = l_Lean_getMainVersoModuleDocs(v_env_1558_);
v___x_1560_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1559_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1540_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___y_1550_ = v___x_1561_;
v___y_1551_ = v___x_1562_;
goto v___jp_1549_;
}
else
{
lean_object* v_val_1563_; 
v_val_1563_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v___x_1560_, 1);
v_val_1556_ = v_val_1563_;
goto v___jp_1555_;
}
}
else
{
lean_object* v_val_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_val_1564_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_val_1564_, v___x_1565_);
lean_dec(v_val_1564_);
v_val_1556_ = v___x_1566_;
goto v___jp_1555_;
}
v___jp_1549_:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1552_, 0, v_range_1539_);
lean_closure_set(v___x_1552_, 1, v___y_1550_);
lean_closure_set(v___x_1552_, 2, v___y_1551_);
v___x_1553_ = 0;
v___x_1554_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1552_, v___x_1553_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
return v___x_1554_;
}
v___jp_1555_:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1540_);
v___y_1550_ = v___x_1557_;
v___y_1551_ = v_val_1556_;
goto v___jp_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1567_, lean_object* v_doc_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_versoModDocString(v_range_1567_, v_doc_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_doc_1568_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1586_, lean_object* v_docComment_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1596_ = l_Lean_versoDocStringOfText(v_declName_1586_, v___x_1595_, v_docComment_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1597_, lean_object* v_docComment_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_versoDocStringFromString(v_declName_1597_, v_docComment_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1607_, lean_object* v_declName_1608_, lean_object* v_env_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = l_Lean_docStringExt;
v___x_1611_ = l_String_removeLeadingSpaces(v_docString_1607_);
v___x_1612_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1610_, v_env_1609_, v_declName_1608_, v___x_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1613_, lean_object* v_modifyEnv_1614_, lean_object* v_docString_1615_){
_start:
{
lean_object* v___f_1616_; lean_object* v___x_1617_; 
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1616_, 0, v_docString_1615_);
lean_closure_set(v___f_1616_, 1, v_declName_1613_);
v___x_1617_ = lean_apply_1(v_modifyEnv_1614_, v___f_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_docComment_1620_, lean_object* v_toBind_1621_, lean_object* v___f_1622_, lean_object* v_____r_1623_){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = l_Lean_getDocStringText___redArg(v_inst_1618_, v_inst_1619_, v_docComment_1620_);
v___x_1625_ = lean_apply_4(v_toBind_1621_, lean_box(0), lean_box(0), v___x_1624_, v___f_1622_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_docComment_1631_, lean_object* v_toBind_1632_, lean_object* v___f_1633_, lean_object* v_____r_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = l_Lean_validateDocComment___redArg(v_inst_1626_, v_inst_1627_, v_inst_1628_, v_inst_1629_, v_inst_1630_, v_docComment_1631_);
v___x_1636_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1635_, v___f_1633_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_docComment_1642_, lean_object* v_toBind_1643_, lean_object* v___f_1644_, lean_object* v_____r_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_docComment_1642_, v_toBind_1643_, v___f_1644_, v_____r_1645_);
lean_dec(v_docComment_1642_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1647_, lean_object* v_____r_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_apply_1(v___f_1647_, v_____r_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_1656_, lean_object* v_declName_1657_, uint8_t v___x_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_toBind_1661_, lean_object* v___f_1662_, lean_object* v_____do__lift_1663_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1663_, v_declName_1657_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_dec(v___f_1662_);
lean_dec(v_toBind_1661_);
lean_dec_ref(v_inst_1660_);
lean_dec_ref(v_inst_1659_);
lean_dec(v_declName_1657_);
goto v___jp_1664_;
}
else
{
lean_dec_ref_known(v___x_1667_, 1);
if (v___x_1658_ == 0)
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
lean_dec(v___f_1656_);
v___x_1668_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1669_ = l_Lean_MessageData_ofConstName(v_declName_1657_, v___x_1658_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_throwError___redArg(v_inst_1659_, v_inst_1660_, v___x_1672_);
v___x_1674_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v___x_1673_, v___f_1662_);
return v___x_1674_;
}
else
{
lean_dec(v___f_1662_);
lean_dec(v_toBind_1661_);
lean_dec_ref(v_inst_1660_);
lean_dec_ref(v_inst_1659_);
lean_dec(v_declName_1657_);
goto v___jp_1664_;
}
}
v___jp_1664_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_apply_1(v___f_1656_, v___x_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_1675_, lean_object* v_declName_1676_, lean_object* v___x_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_toBind_1680_, lean_object* v___f_1681_, lean_object* v_____do__lift_1682_){
_start:
{
uint8_t v___x_247__boxed_1683_; lean_object* v_res_1684_; 
v___x_247__boxed_1683_ = lean_unbox(v___x_1677_);
v_res_1684_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1675_, v_declName_1676_, v___x_247__boxed_1683_, v_inst_1678_, v_inst_1679_, v_toBind_1680_, v___f_1681_, v_____do__lift_1682_);
lean_dec_ref(v_____do__lift_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_declName_1692_, lean_object* v_docComment_1693_){
_start:
{
lean_object* v_toApplicative_1694_; lean_object* v_toBind_1695_; lean_object* v_toPure_1696_; uint8_t v___x_1697_; 
v_toApplicative_1694_ = lean_ctor_get(v_inst_1685_, 0);
v_toBind_1695_ = lean_ctor_get(v_inst_1685_, 1);
lean_inc(v_toBind_1695_);
v_toPure_1696_ = lean_ctor_get(v_toApplicative_1694_, 1);
v___x_1697_ = l_Lean_Name_isAnonymous(v_declName_1692_);
if (v___x_1697_ == 0)
{
lean_object* v_getEnv_1698_; lean_object* v_modifyEnv_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___f_1705_; lean_object* v___x_1706_; 
v_getEnv_1698_ = lean_ctor_get(v_inst_1688_, 0);
lean_inc(v_getEnv_1698_);
v_modifyEnv_1699_ = lean_ctor_get(v_inst_1688_, 1);
lean_inc(v_modifyEnv_1699_);
lean_dec_ref(v_inst_1688_);
lean_inc(v_declName_1692_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1700_, 0, v_declName_1692_);
lean_closure_set(v___f_1700_, 1, v_modifyEnv_1699_);
lean_inc_n(v_toBind_1695_, 3);
lean_inc(v_docComment_1693_);
lean_inc_ref(v_inst_1689_);
lean_inc_ref_n(v_inst_1685_, 2);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1701_, 0, v_inst_1685_);
lean_closure_set(v___f_1701_, 1, v_inst_1689_);
lean_closure_set(v___f_1701_, 2, v_docComment_1693_);
lean_closure_set(v___f_1701_, 3, v_toBind_1695_);
lean_closure_set(v___f_1701_, 4, v___f_1700_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1702_, 0, v_inst_1685_);
lean_closure_set(v___f_1702_, 1, v_inst_1686_);
lean_closure_set(v___f_1702_, 2, v_inst_1690_);
lean_closure_set(v___f_1702_, 3, v_inst_1691_);
lean_closure_set(v___f_1702_, 4, v_inst_1687_);
lean_closure_set(v___f_1702_, 5, v_docComment_1693_);
lean_closure_set(v___f_1702_, 6, v_toBind_1695_);
lean_closure_set(v___f_1702_, 7, v___f_1701_);
lean_inc_ref(v___f_1702_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1703_, 0, v___f_1702_);
v___x_1704_ = lean_box(v___x_1697_);
v___f_1705_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1705_, 0, v___f_1702_);
lean_closure_set(v___f_1705_, 1, v_declName_1692_);
lean_closure_set(v___f_1705_, 2, v___x_1704_);
lean_closure_set(v___f_1705_, 3, v_inst_1685_);
lean_closure_set(v___f_1705_, 4, v_inst_1689_);
lean_closure_set(v___f_1705_, 5, v_toBind_1695_);
lean_closure_set(v___f_1705_, 6, v___f_1703_);
v___x_1706_ = lean_apply_4(v_toBind_1695_, lean_box(0), lean_box(0), v_getEnv_1698_, v___f_1705_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_inc(v_toPure_1696_);
lean_dec(v_toBind_1695_);
lean_dec(v_docComment_1693_);
lean_dec(v_declName_1692_);
lean_dec(v_inst_1691_);
lean_dec_ref(v_inst_1690_);
lean_dec_ref(v_inst_1689_);
lean_dec_ref(v_inst_1688_);
lean_dec(v_inst_1687_);
lean_dec(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_apply_2(v_toPure_1696_, lean_box(0), v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_declName_1717_, lean_object* v_docComment_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_addMarkdownDocString___redArg(v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_inst_1714_, v_inst_1715_, v_inst_1716_, v_declName_1717_, v_docComment_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_1720_, lean_object* v_x1_1721_, lean_object* v_x2_1722_){
_start:
{
lean_object* v_index_1723_; lean_object* v_sourceString_1724_; lean_object* v_imports_1725_; lean_object* v_currNamespace_1726_; lean_object* v_openDecls_1727_; lean_object* v_options_1728_; lean_object* v_check_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1742_; 
v_index_1723_ = lean_ctor_get(v_x2_1722_, 1);
v_sourceString_1724_ = lean_ctor_get(v_x2_1722_, 2);
v_imports_1725_ = lean_ctor_get(v_x2_1722_, 3);
v_currNamespace_1726_ = lean_ctor_get(v_x2_1722_, 4);
v_openDecls_1727_ = lean_ctor_get(v_x2_1722_, 5);
v_options_1728_ = lean_ctor_get(v_x2_1722_, 6);
v_check_1729_ = lean_ctor_get(v_x2_1722_, 7);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_x2_1722_);
if (v_isSharedCheck_1742_ == 0)
{
lean_object* v_unused_1743_; 
v_unused_1743_ = lean_ctor_get(v_x2_1722_, 0);
lean_dec(v_unused_1743_);
v___x_1731_ = v_x2_1722_;
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_check_1729_);
lean_inc(v_options_1728_);
lean_inc(v_openDecls_1727_);
lean_inc(v_currNamespace_1726_);
lean_inc(v_imports_1725_);
lean_inc(v_sourceString_1724_);
lean_inc(v_index_1723_);
lean_dec(v_x2_1722_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v_toEnvExtension_1734_; lean_object* v_asyncMode_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1733_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1734_ = lean_ctor_get(v___x_1733_, 0);
v_asyncMode_1735_ = lean_ctor_get(v_toEnvExtension_1734_, 2);
v___x_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1736_, 0, v_declName_1720_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1736_);
v___x_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_index_1723_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_sourceString_1724_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_imports_1725_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_currNamespace_1726_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_openDecls_1727_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v_options_1728_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_check_1729_);
v___x_1738_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_box(0);
v___x_1740_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1733_, v_x1_1721_, v___x_1738_, v_asyncMode_1735_, v___x_1739_);
return v___x_1740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1763_, lean_object* v_docs_1764_, lean_object* v_deferred_1765_, lean_object* v___f_1766_, lean_object* v_env_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v_env_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1768_ = l_Lean_versoDocStringExt;
v_env_1769_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1768_, v_env_1767_, v_declName_1763_, v_docs_1764_);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_array_get_size(v_deferred_1765_);
v___x_1772_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_1773_ = lean_nat_dec_lt(v___x_1770_, v___x_1771_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v___f_1766_);
lean_dec_ref(v_deferred_1765_);
return v_env_1769_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v___x_1771_, v___x_1771_);
if (v___x_1774_ == 0)
{
if (v___x_1773_ == 0)
{
lean_dec_ref(v___f_1766_);
lean_dec_ref(v_deferred_1765_);
return v_env_1769_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1771_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1772_, v___f_1766_, v_deferred_1765_, v___x_1775_, v___x_1776_, v_env_1769_);
return v___x_1777_;
}
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = lean_usize_of_nat(v___x_1771_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1772_, v___f_1766_, v_deferred_1765_, v___x_1778_, v___x_1779_, v_env_1769_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_1781_, lean_object* v___f_1782_, lean_object* v_____r_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_apply_1(v_modifyEnv_1781_, v___f_1782_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_1787_, lean_object* v_modifyEnv_1788_, lean_object* v___f_1789_, uint8_t v___x_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_toBind_1793_, lean_object* v___f_1794_, lean_object* v_____do__lift_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1795_, v_declName_1787_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1797_; 
lean_dec(v___f_1794_);
lean_dec(v_toBind_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec(v_declName_1787_);
v___x_1797_ = lean_apply_1(v_modifyEnv_1788_, v___f_1789_);
return v___x_1797_;
}
else
{
lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1814_; 
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1814_ == 0)
{
lean_object* v_unused_1815_; 
v_unused_1815_ = lean_ctor_get(v___x_1796_, 0);
lean_dec(v_unused_1815_);
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1814_;
goto v_resetjp_1798_;
}
else
{
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1814_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
if (v___x_1790_ == 0)
{
lean_object* v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1808_; 
lean_dec_ref(v___f_1789_);
lean_dec(v_modifyEnv_1788_);
v___x_1801_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_1802_ = 1;
v___x_1803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1787_, v___x_1802_);
v___x_1804_ = lean_string_append(v___x_1801_, v___x_1803_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_1806_ = lean_string_append(v___x_1804_, v___x_1805_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 3);
lean_ctor_set(v___x_1799_, 0, v___x_1806_);
v___x_1808_ = v___x_1799_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = l_Lean_MessageData_ofFormat(v___x_1808_);
v___x_1810_ = l_Lean_throwError___redArg(v_inst_1791_, v_inst_1792_, v___x_1809_);
v___x_1811_ = lean_apply_4(v_toBind_1793_, lean_box(0), lean_box(0), v___x_1810_, v___f_1794_);
return v___x_1811_;
}
}
else
{
lean_object* v___x_1813_; 
lean_del_object(v___x_1799_);
lean_dec(v___f_1794_);
lean_dec(v_toBind_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec_ref(v_inst_1791_);
lean_dec(v_declName_1787_);
v___x_1813_ = lean_apply_1(v_modifyEnv_1788_, v___f_1789_);
return v___x_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1816_, lean_object* v_modifyEnv_1817_, lean_object* v___f_1818_, lean_object* v___x_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_toBind_1822_, lean_object* v___f_1823_, lean_object* v_____do__lift_1824_){
_start:
{
uint8_t v___x_374__boxed_1825_; lean_object* v_res_1826_; 
v___x_374__boxed_1825_ = lean_unbox(v___x_1819_);
v_res_1826_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_1816_, v_modifyEnv_1817_, v___f_1818_, v___x_374__boxed_1825_, v_inst_1820_, v_inst_1821_, v_toBind_1822_, v___f_1823_, v_____do__lift_1824_);
lean_dec_ref(v_____do__lift_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_declName_1830_, lean_object* v_docs_1831_, lean_object* v_deferred_1832_){
_start:
{
lean_object* v_toApplicative_1833_; lean_object* v_toBind_1834_; lean_object* v_toPure_1835_; uint8_t v___x_1836_; 
v_toApplicative_1833_ = lean_ctor_get(v_inst_1827_, 0);
v_toBind_1834_ = lean_ctor_get(v_inst_1827_, 1);
lean_inc(v_toBind_1834_);
v_toPure_1835_ = lean_ctor_get(v_toApplicative_1833_, 1);
v___x_1836_ = l_Lean_Name_isAnonymous(v_declName_1830_);
if (v___x_1836_ == 0)
{
lean_object* v_getEnv_1837_; lean_object* v_modifyEnv_1838_; lean_object* v___f_1839_; lean_object* v___f_1840_; lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; 
v_getEnv_1837_ = lean_ctor_get(v_inst_1828_, 0);
lean_inc(v_getEnv_1837_);
v_modifyEnv_1838_ = lean_ctor_get(v_inst_1828_, 1);
lean_inc_n(v_modifyEnv_1838_, 2);
lean_dec_ref(v_inst_1828_);
lean_inc_n(v_declName_1830_, 2);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1839_, 0, v_declName_1830_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1840_, 0, v_declName_1830_);
lean_closure_set(v___f_1840_, 1, v_docs_1831_);
lean_closure_set(v___f_1840_, 2, v_deferred_1832_);
lean_closure_set(v___f_1840_, 3, v___f_1839_);
lean_inc_ref(v___f_1840_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1841_, 0, v_modifyEnv_1838_);
lean_closure_set(v___f_1841_, 1, v___f_1840_);
v___x_1842_ = lean_box(v___x_1836_);
lean_inc(v_toBind_1834_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1843_, 0, v_declName_1830_);
lean_closure_set(v___f_1843_, 1, v_modifyEnv_1838_);
lean_closure_set(v___f_1843_, 2, v___f_1840_);
lean_closure_set(v___f_1843_, 3, v___x_1842_);
lean_closure_set(v___f_1843_, 4, v_inst_1827_);
lean_closure_set(v___f_1843_, 5, v_inst_1829_);
lean_closure_set(v___f_1843_, 6, v_toBind_1834_);
lean_closure_set(v___f_1843_, 7, v___f_1841_);
v___x_1844_ = lean_apply_4(v_toBind_1834_, lean_box(0), lean_box(0), v_getEnv_1837_, v___f_1843_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_inc(v_toPure_1835_);
lean_dec(v_toBind_1834_);
lean_dec_ref(v_deferred_1832_);
lean_dec_ref(v_docs_1831_);
lean_dec(v_declName_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v_inst_1827_);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_apply_2(v_toPure_1835_, lean_box(0), v___x_1845_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_declName_1852_, lean_object* v_docs_1853_, lean_object* v_deferred_1854_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1848_, v_inst_1849_, v_inst_1851_, v_declName_1852_, v_docs_1853_, v_deferred_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_, lean_object* v_declName_1861_, lean_object* v_docs_1862_, lean_object* v_deferred_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_addVersoDocStringCore(v_m_1856_, v_inst_1857_, v_inst_1858_, v_inst_1859_, v_inst_1860_, v_declName_1861_, v_docs_1862_, v_deferred_1863_);
lean_dec(v_inst_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_1865_, lean_object* v_x1_1866_, lean_object* v_x2_1867_){
_start:
{
lean_object* v_index_1868_; lean_object* v_sourceString_1869_; lean_object* v_imports_1870_; lean_object* v_currNamespace_1871_; lean_object* v_openDecls_1872_; lean_object* v_options_1873_; lean_object* v_check_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1887_; 
v_index_1868_ = lean_ctor_get(v_x2_1867_, 1);
v_sourceString_1869_ = lean_ctor_get(v_x2_1867_, 2);
v_imports_1870_ = lean_ctor_get(v_x2_1867_, 3);
v_currNamespace_1871_ = lean_ctor_get(v_x2_1867_, 4);
v_openDecls_1872_ = lean_ctor_get(v_x2_1867_, 5);
v_options_1873_ = lean_ctor_get(v_x2_1867_, 6);
v_check_1874_ = lean_ctor_get(v_x2_1867_, 7);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x2_1867_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v_x2_1867_, 0);
lean_dec(v_unused_1888_);
v___x_1876_ = v_x2_1867_;
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_check_1874_);
lean_inc(v_options_1873_);
lean_inc(v_openDecls_1872_);
lean_inc(v_currNamespace_1871_);
lean_inc(v_imports_1870_);
lean_inc(v_sourceString_1869_);
lean_inc(v_index_1868_);
lean_dec(v_x2_1867_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v_toEnvExtension_1879_; lean_object* v_asyncMode_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1878_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1879_ = lean_ctor_get(v___x_1878_, 0);
v_asyncMode_1880_ = lean_ctor_get(v_toEnvExtension_1879_, 2);
v___x_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1881_, 0, v_size_1865_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1881_);
v___x_1883_ = v___x_1876_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_index_1868_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_sourceString_1869_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_imports_1870_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v_currNamespace_1871_);
lean_ctor_set(v_reuseFailAlloc_1886_, 5, v_openDecls_1872_);
lean_ctor_set(v_reuseFailAlloc_1886_, 6, v_options_1873_);
lean_ctor_set(v_reuseFailAlloc_1886_, 7, v_check_1874_);
v___x_1883_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_box(0);
v___x_1885_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1878_, v_x1_1866_, v___x_1883_, v_asyncMode_1880_, v___x_1884_);
return v___x_1885_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_1891_ = l_Lean_stringToMessageData(v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_1892_, lean_object* v_inst_1893_, lean_object* v_inst_1894_, lean_object* v_deferred_1895_, lean_object* v_inst_1896_, lean_object* v___f_1897_, lean_object* v_____do__lift_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1898_, v_docs_1892_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref(v___f_1897_);
lean_dec_ref(v_inst_1896_);
lean_dec_ref(v_deferred_1895_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_1902_ = l_Lean_stringToMessageData(v_a_1900_);
v___x_1903_ = l_Lean_indentD(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l_Lean_throwError___redArg(v_inst_1893_, v_inst_1894_, v___x_1904_);
return v___x_1905_;
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
lean_dec_ref(v_inst_1894_);
lean_dec_ref(v_inst_1893_);
v_a_1906_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_array_get_size(v_deferred_1895_);
v___x_1909_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_1910_ = lean_nat_dec_lt(v___x_1907_, v___x_1908_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec_ref(v___f_1897_);
lean_dec_ref(v_deferred_1895_);
v___x_1911_ = l_Lean_setEnv___redArg(v_inst_1896_, v_a_1906_);
return v___x_1911_;
}
else
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1912_ == 0)
{
if (v___x_1910_ == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref(v___f_1897_);
lean_dec_ref(v_deferred_1895_);
v___x_1913_ = l_Lean_setEnv___redArg(v_inst_1896_, v_a_1906_);
return v___x_1913_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1908_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1909_, v___f_1897_, v_deferred_1895_, v___x_1914_, v___x_1915_, v_a_1906_);
v___x_1917_ = l_Lean_setEnv___redArg(v_inst_1896_, v___x_1916_);
return v___x_1917_;
}
}
else
{
size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1908_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1909_, v___f_1897_, v_deferred_1895_, v___x_1918_, v___x_1919_, v_a_1906_);
v___x_1921_ = l_Lean_setEnv___redArg(v_inst_1896_, v___x_1920_);
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_deferred_1925_, lean_object* v_inst_1926_, lean_object* v_toBind_1927_, lean_object* v_getEnv_1928_, lean_object* v_____do__lift_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v_size_1931_; lean_object* v___f_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; 
v___x_1930_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1929_);
v_size_1931_ = lean_ctor_get(v___x_1930_, 2);
lean_inc(v_size_1931_);
lean_dec_ref(v___x_1930_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1932_, 0, v_size_1931_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1933_, 0, v_docs_1922_);
lean_closure_set(v___f_1933_, 1, v_inst_1923_);
lean_closure_set(v___f_1933_, 2, v_inst_1924_);
lean_closure_set(v___f_1933_, 3, v_deferred_1925_);
lean_closure_set(v___f_1933_, 4, v_inst_1926_);
lean_closure_set(v___f_1933_, 5, v___f_1932_);
v___x_1934_ = lean_apply_4(v_toBind_1927_, lean_box(0), lean_box(0), v_getEnv_1928_, v___f_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_1937_ = l_Lean_stringToMessageData(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_toBind_1940_, lean_object* v_getEnv_1941_, lean_object* v___f_1942_, lean_object* v_____do__lift_1943_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1944_ = l_Lean_getMainModuleDoc(v_____do__lift_1943_);
v___x_1945_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_1944_);
lean_dec_ref(v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
lean_dec(v___f_1942_);
lean_dec(v_getEnv_1941_);
lean_dec(v_toBind_1940_);
v___x_1946_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_1947_ = l_Lean_throwError___redArg(v_inst_1938_, v_inst_1939_, v___x_1946_);
return v___x_1947_;
}
else
{
lean_object* v___x_1948_; 
lean_dec_ref(v_inst_1939_);
lean_dec_ref(v_inst_1938_);
v___x_1948_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v_getEnv_1941_, v___f_1942_);
return v___x_1948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_1949_, lean_object* v_inst_1950_, lean_object* v_inst_1951_, lean_object* v_docs_1952_, lean_object* v_deferred_1953_){
_start:
{
lean_object* v_toBind_1954_; lean_object* v_getEnv_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; 
v_toBind_1954_ = lean_ctor_get(v_inst_1949_, 1);
lean_inc_n(v_toBind_1954_, 3);
v_getEnv_1955_ = lean_ctor_get(v_inst_1950_, 0);
lean_inc_n(v_getEnv_1955_, 3);
lean_inc_ref(v_inst_1951_);
lean_inc_ref(v_inst_1949_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1956_, 0, v_docs_1952_);
lean_closure_set(v___f_1956_, 1, v_inst_1949_);
lean_closure_set(v___f_1956_, 2, v_inst_1951_);
lean_closure_set(v___f_1956_, 3, v_deferred_1953_);
lean_closure_set(v___f_1956_, 4, v_inst_1950_);
lean_closure_set(v___f_1956_, 5, v_toBind_1954_);
lean_closure_set(v___f_1956_, 6, v_getEnv_1955_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1957_, 0, v_inst_1949_);
lean_closure_set(v___f_1957_, 1, v_inst_1951_);
lean_closure_set(v___f_1957_, 2, v_toBind_1954_);
lean_closure_set(v___f_1957_, 3, v_getEnv_1955_);
lean_closure_set(v___f_1957_, 4, v___f_1956_);
v___x_1958_ = lean_apply_4(v_toBind_1954_, lean_box(0), lean_box(0), v_getEnv_1955_, v___f_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_inst_1963_, lean_object* v_docs_1964_, lean_object* v_deferred_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_1960_, v_inst_1961_, v_inst_1963_, v_docs_1964_, v_deferred_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_docs_1972_, lean_object* v_deferred_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_addVersoModDocStringCore(v_m_1967_, v_inst_1968_, v_inst_1969_, v_inst_1970_, v_inst_1971_, v_docs_1972_, v_deferred_1973_);
lean_dec(v_inst_1970_);
return v_res_1974_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_box(1);
v___x_1976_ = l_Lean_MessageData_ofFormat(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2));
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
if (lean_obj_tag(v_x_1983_) == 0)
{
return v_x_1982_;
}
else
{
lean_object* v_head_1984_; lean_object* v_tail_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2007_; 
v_head_1984_ = lean_ctor_get(v_x_1983_, 0);
v_tail_1985_ = lean_ctor_get(v_x_1983_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1987_ = v_x_1983_;
v_isShared_1988_ = v_isSharedCheck_2007_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_tail_1985_);
lean_inc(v_head_1984_);
lean_dec(v_x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2007_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v_before_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2005_; 
v_before_1989_ = lean_ctor_get(v_head_1984_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_head_1984_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v_head_1984_, 1);
lean_dec(v_unused_2006_);
v___x_1991_ = v_head_1984_;
v_isShared_1992_ = v_isSharedCheck_2005_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_before_1989_);
lean_dec(v_head_1984_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2005_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 7);
lean_ctor_set(v___x_1991_, 1, v___x_1993_);
lean_ctor_set(v___x_1991_, 0, v_x_1982_);
v___x_1995_ = v___x_1991_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_x_1982_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1996_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 7);
lean_ctor_set(v___x_1987_, 1, v___x_1996_);
lean_ctor_set(v___x_1987_, 0, v___x_1995_);
v___x_1998_ = v___x_1987_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = l_Lean_MessageData_ofSyntax(v_before_1989_);
v___x_2000_ = l_Lean_indentD(v___x_1999_);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v_x_1982_ = v___x_2001_;
v_x_1983_ = v_tail_1985_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1));
v___x_2012_ = l_Lean_MessageData_ofFormat(v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object* v_msgData_2013_, lean_object* v_macroStack_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_toCold_2017_; lean_object* v_options_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_toCold_2017_ = lean_ctor_get(v___y_2015_, 0);
v_options_2018_ = lean_ctor_get(v_toCold_2017_, 2);
v___x_2019_ = l_Lean_Elab_pp_macroStack;
v___x_2020_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_options_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec(v_macroStack_2014_);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_msgData_2013_);
return v___x_2021_;
}
else
{
if (lean_obj_tag(v_macroStack_2014_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_msgData_2013_);
return v___x_2022_;
}
else
{
lean_object* v_head_2023_; lean_object* v_after_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2039_; 
v_head_2023_ = lean_ctor_get(v_macroStack_2014_, 0);
lean_inc(v_head_2023_);
v_after_2024_ = lean_ctor_get(v_head_2023_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_head_2023_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v_head_2023_, 0);
lean_dec(v_unused_2040_);
v___x_2026_ = v_head_2023_;
v_isShared_2027_ = v_isSharedCheck_2039_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_after_2024_);
lean_dec(v_head_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2039_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set_tag(v___x_2026_, 7);
lean_ctor_set(v___x_2026_, 1, v___x_2028_);
lean_ctor_set(v___x_2026_, 0, v_msgData_2013_);
v___x_2030_ = v___x_2026_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_msgData_2013_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v_msgData_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2031_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_MessageData_ofSyntax(v_after_2024_);
v___x_2034_ = l_Lean_indentD(v___x_2033_);
v_msgData_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2035_, 0, v___x_2032_);
lean_ctor_set(v_msgData_2035_, 1, v___x_2034_);
v___x_2036_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(v_msgData_2035_, v_macroStack_2014_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2041_, lean_object* v_macroStack_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2041_, v_macroStack_2042_, v___y_2043_);
lean_dec_ref(v___y_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_ref_2054_; lean_object* v_macroStack_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_ref_2054_ = lean_ctor_get(v___y_2051_, 2);
v_macroStack_2055_ = lean_ctor_get(v___y_2047_, 1);
v___x_2056_ = l_Lean_Elab_getBetterRef(v_ref_2054_, v_macroStack_2055_);
v___x_2057_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2046_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
lean_inc(v_macroStack_2055_);
v___x_2059_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_a_2058_, v_macroStack_2055_, v___y_2051_);
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2056_);
lean_ctor_set(v___x_2064_, 1, v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2078_, lean_object* v_as_2079_, size_t v_i_2080_, size_t v_stop_2081_, lean_object* v_b_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_eq(v_i_2080_, v_stop_2081_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v_index_2085_; lean_object* v_sourceString_2086_; lean_object* v_imports_2087_; lean_object* v_currNamespace_2088_; lean_object* v_openDecls_2089_; lean_object* v_options_2090_; lean_object* v_check_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2107_; 
v___x_2084_ = lean_array_uget(v_as_2079_, v_i_2080_);
v_index_2085_ = lean_ctor_get(v___x_2084_, 1);
v_sourceString_2086_ = lean_ctor_get(v___x_2084_, 2);
v_imports_2087_ = lean_ctor_get(v___x_2084_, 3);
v_currNamespace_2088_ = lean_ctor_get(v___x_2084_, 4);
v_openDecls_2089_ = lean_ctor_get(v___x_2084_, 5);
v_options_2090_ = lean_ctor_get(v___x_2084_, 6);
v_check_2091_ = lean_ctor_get(v___x_2084_, 7);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; 
v_unused_2108_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2108_);
v___x_2093_ = v___x_2084_;
v_isShared_2094_ = v_isSharedCheck_2107_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_check_2091_);
lean_inc(v_options_2090_);
lean_inc(v_openDecls_2089_);
lean_inc(v_currNamespace_2088_);
lean_inc(v_imports_2087_);
lean_inc(v_sourceString_2086_);
lean_inc(v_index_2085_);
lean_dec(v___x_2084_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2107_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v_toEnvExtension_2096_; lean_object* v_asyncMode_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2095_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2096_ = lean_ctor_get(v___x_2095_, 0);
v_asyncMode_2097_ = lean_ctor_get(v_toEnvExtension_2096_, 2);
lean_inc(v_declName_2078_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_declName_2078_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2098_);
v___x_2100_ = v___x_2093_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_index_2085_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_sourceString_2086_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_imports_2087_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_currNamespace_2088_);
lean_ctor_set(v_reuseFailAlloc_2106_, 5, v_openDecls_2089_);
lean_ctor_set(v_reuseFailAlloc_2106_, 6, v_options_2090_);
lean_ctor_set(v_reuseFailAlloc_2106_, 7, v_check_2091_);
v___x_2100_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2095_, v_b_2082_, v___x_2100_, v_asyncMode_2097_, v___x_2101_);
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_i_2080_, v___x_2103_);
v_i_2080_ = v___x_2104_;
v_b_2082_ = v___x_2102_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2078_);
return v_b_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2109_, lean_object* v_as_2110_, lean_object* v_i_2111_, lean_object* v_stop_2112_, lean_object* v_b_2113_){
_start:
{
size_t v_i_boxed_2114_; size_t v_stop_boxed_2115_; lean_object* v_res_2116_; 
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_stop_boxed_2115_ = lean_unbox_usize(v_stop_2112_);
lean_dec(v_stop_2112_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2109_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_, v_b_2113_);
lean_dec_ref(v_as_2110_);
return v_res_2116_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
lean_ctor_set(v___x_2122_, 2, v___x_2121_);
lean_ctor_set(v___x_2122_, 3, v___x_2121_);
lean_ctor_set(v___x_2122_, 4, v___x_2121_);
lean_ctor_set(v___x_2122_, 5, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2123_, lean_object* v_docs_2124_, lean_object* v_deferred_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2165_; lean_object* v___y_2166_; uint8_t v___x_2184_; 
v___x_2184_ = l_Lean_Name_isAnonymous(v_declName_2123_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; lean_object* v_env_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_st_ref_get(v___y_2131_);
v_env_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc_ref(v_env_2186_);
lean_dec(v___x_2185_);
v___x_2187_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2186_, v_declName_2123_);
lean_dec_ref(v_env_2186_);
if (lean_obj_tag(v___x_2187_) == 0)
{
v___y_2165_ = v___y_2129_;
v___y_2166_ = v___y_2131_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2187_, 0);
lean_dec(v_unused_2203_);
v___x_2189_ = v___x_2187_;
v_isShared_2190_ = v_isSharedCheck_2202_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v___x_2187_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2202_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
if (v___x_2184_ == 0)
{
lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_dec_ref(v_docs_2124_);
v___x_2191_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2192_ = 1;
v___x_2193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2123_, v___x_2192_);
v___x_2194_ = lean_string_append(v___x_2191_, v___x_2193_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2196_ = lean_string_append(v___x_2194_, v___x_2195_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set_tag(v___x_2189_, 3);
lean_ctor_set(v___x_2189_, 0, v___x_2196_);
v___x_2198_ = v___x_2189_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
v___x_2200_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2199_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
return v___x_2200_;
}
}
else
{
lean_del_object(v___x_2189_);
v___y_2165_ = v___y_2129_;
v___y_2166_ = v___y_2131_;
goto v___jp_2164_;
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec_ref(v_docs_2124_);
lean_dec(v_declName_2123_);
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
v___jp_2133_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_mctx_2148_; lean_object* v_zetaDeltaFVarIds_2149_; lean_object* v_postponed_2150_; lean_object* v_diag_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2162_; 
v___x_2144_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2145_, 0, v___y_2143_);
lean_ctor_set(v___x_2145_, 1, v___y_2142_);
lean_ctor_set(v___x_2145_, 2, v___y_2134_);
lean_ctor_set(v___x_2145_, 3, v___y_2141_);
lean_ctor_set(v___x_2145_, 4, v___y_2139_);
lean_ctor_set(v___x_2145_, 5, v___x_2144_);
lean_ctor_set(v___x_2145_, 6, v___y_2140_);
lean_ctor_set(v___x_2145_, 7, v___y_2135_);
lean_ctor_set(v___x_2145_, 8, v___y_2137_);
v___x_2146_ = lean_st_ref_put(v___y_2138_, v___x_2145_);
v___x_2147_ = lean_st_ref_take(v___y_2136_);
v_mctx_2148_ = lean_ctor_get(v___x_2147_, 0);
v_zetaDeltaFVarIds_2149_ = lean_ctor_get(v___x_2147_, 2);
v_postponed_2150_ = lean_ctor_get(v___x_2147_, 3);
v_diag_2151_ = lean_ctor_get(v___x_2147_, 4);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v___x_2147_, 1);
lean_dec(v_unused_2163_);
v___x_2153_ = v___x_2147_;
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_diag_2151_);
lean_inc(v_postponed_2150_);
lean_inc(v_zetaDeltaFVarIds_2149_);
lean_inc(v_mctx_2148_);
lean_dec(v___x_2147_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2156_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_mctx_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_zetaDeltaFVarIds_2149_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_postponed_2150_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_diag_2151_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_st_ref_put(v___y_2136_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
return v___x_2160_;
}
}
}
v___jp_2164_:
{
lean_object* v___x_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_traceState_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2176_; lean_object* v_env_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2167_ = lean_st_ref_take(v___y_2166_);
v_env_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc_ref(v_env_2168_);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_nextMacroScope_2169_);
v_ngen_2170_ = lean_ctor_get(v___x_2167_, 2);
lean_inc_ref(v_ngen_2170_);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2167_, 3);
lean_inc_ref(v_auxDeclNGen_2171_);
v_traceState_2172_ = lean_ctor_get(v___x_2167_, 4);
lean_inc_ref(v_traceState_2172_);
v_messages_2173_ = lean_ctor_get(v___x_2167_, 6);
lean_inc_ref(v_messages_2173_);
v_infoState_2174_ = lean_ctor_get(v___x_2167_, 7);
lean_inc_ref(v_infoState_2174_);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2167_, 8);
lean_inc_ref(v_snapshotTasks_2175_);
lean_dec(v___x_2167_);
v___x_2176_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2123_);
v_env_2177_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2176_, v_env_2168_, v_declName_2123_, v_docs_2124_);
v___x_2178_ = lean_unsigned_to_nat(0u);
v___x_2179_ = lean_array_get_size(v_deferred_2125_);
v___x_2180_ = lean_nat_dec_lt(v___x_2178_, v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec(v_declName_2123_);
v___y_2134_ = v_ngen_2170_;
v___y_2135_ = v_infoState_2174_;
v___y_2136_ = v___y_2165_;
v___y_2137_ = v_snapshotTasks_2175_;
v___y_2138_ = v___y_2166_;
v___y_2139_ = v_traceState_2172_;
v___y_2140_ = v_messages_2173_;
v___y_2141_ = v_auxDeclNGen_2171_;
v___y_2142_ = v_nextMacroScope_2169_;
v___y_2143_ = v_env_2177_;
goto v___jp_2133_;
}
else
{
size_t v___x_2181_; size_t v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((size_t)0ULL);
v___x_2182_ = lean_usize_of_nat(v___x_2179_);
v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2123_, v_deferred_2125_, v___x_2181_, v___x_2182_, v_env_2177_);
v___y_2134_ = v_ngen_2170_;
v___y_2135_ = v_infoState_2174_;
v___y_2136_ = v___y_2165_;
v___y_2137_ = v_snapshotTasks_2175_;
v___y_2138_ = v___y_2166_;
v___y_2139_ = v_traceState_2172_;
v___y_2140_ = v_messages_2173_;
v___y_2141_ = v_auxDeclNGen_2171_;
v___y_2142_ = v_nextMacroScope_2169_;
v___y_2143_ = v___x_2183_;
goto v___jp_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2206_, lean_object* v_docs_2207_, lean_object* v_deferred_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2206_, v_docs_2207_, v_deferred_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_deferred_2208_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2217_, lean_object* v_binders_2218_, lean_object* v_docComment_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___x_2247_; lean_object* v_env_2248_; lean_object* v___x_2249_; 
v___x_2247_ = lean_st_ref_get(v_a_2225_);
v_env_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_env_2248_);
lean_dec(v___x_2247_);
v___x_2249_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2248_, v_declName_2217_);
lean_dec_ref(v_env_2248_);
if (lean_obj_tag(v___x_2249_) == 0)
{
v___y_2228_ = v_a_2220_;
v___y_2229_ = v_a_2221_;
v___y_2230_ = v_a_2222_;
v___y_2231_ = v_a_2223_;
v___y_2232_ = v_a_2224_;
v___y_2233_ = v_a_2225_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_binders_2218_);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v___x_2249_, 0);
lean_dec(v_unused_2265_);
v___x_2251_ = v___x_2249_;
v_isShared_2252_ = v_isSharedCheck_2264_;
goto v_resetjp_2250_;
}
else
{
lean_dec(v___x_2249_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2264_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2253_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2254_ = 1;
v___x_2255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2217_, v___x_2254_);
v___x_2256_ = lean_string_append(v___x_2253_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2258_ = lean_string_append(v___x_2256_, v___x_2257_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 3);
lean_ctor_set(v___x_2251_, 0, v___x_2258_);
v___x_2260_ = v___x_2251_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = l_Lean_MessageData_ofFormat(v___x_2260_);
v___x_2262_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2261_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2262_;
}
}
}
v___jp_2227_:
{
lean_object* v___x_2234_; 
lean_inc(v_declName_2217_);
v___x_2234_ = l_Lean_versoDocString(v_declName_2217_, v_binders_2218_, v_docComment_2219_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_toVersoDocString_2236_; lean_object* v_deferredChecks_2237_; lean_object* v___x_2238_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_toVersoDocString_2236_ = lean_ctor_get(v_a_2235_, 0);
lean_inc_ref(v_toVersoDocString_2236_);
v_deferredChecks_2237_ = lean_ctor_get(v_a_2235_, 1);
lean_inc_ref(v_deferredChecks_2237_);
lean_dec(v_a_2235_);
v___x_2238_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2217_, v_toVersoDocString_2236_, v_deferredChecks_2237_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec_ref(v_deferredChecks_2237_);
return v___x_2238_;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_declName_2217_);
v_a_2239_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2234_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2234_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2266_, lean_object* v_binders_2267_, lean_object* v_docComment_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_addVersoDocString(v_declName_2266_, v_binders_2267_, v_docComment_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_a_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_a_2269_);
lean_dec(v_docComment_2268_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2277_, lean_object* v_msg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2287_, v_msg_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object* v_msgData_2297_, lean_object* v_macroStack_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2297_, v_macroStack_2298_, v___y_2303_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object* v_msgData_2307_, lean_object* v_macroStack_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2307_, v_macroStack_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2317_, lean_object* v_docComment_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___x_2346_; lean_object* v_env_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_st_ref_get(v_a_2324_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc_ref(v_env_2347_);
lean_dec(v___x_2346_);
v___x_2348_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2347_, v_declName_2317_);
lean_dec_ref(v_env_2347_);
if (lean_obj_tag(v___x_2348_) == 0)
{
v___y_2327_ = v_a_2319_;
v___y_2328_ = v_a_2320_;
v___y_2329_ = v_a_2321_;
v___y_2330_ = v_a_2322_;
v___y_2331_ = v_a_2323_;
v___y_2332_ = v_a_2324_;
goto v___jp_2326_;
}
else
{
lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_docComment_2318_);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2364_);
v___x_2350_ = v___x_2348_;
v_isShared_2351_ = v_isSharedCheck_2363_;
goto v_resetjp_2349_;
}
else
{
lean_dec(v___x_2348_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2363_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2352_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2353_ = 1;
v___x_2354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2317_, v___x_2353_);
v___x_2355_ = lean_string_append(v___x_2352_, v___x_2354_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2357_ = lean_string_append(v___x_2355_, v___x_2356_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 3);
lean_ctor_set(v___x_2350_, 0, v___x_2357_);
v___x_2359_ = v___x_2350_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = l_Lean_MessageData_ofFormat(v___x_2359_);
v___x_2361_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2360_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2361_;
}
}
}
v___jp_2326_:
{
lean_object* v___x_2333_; 
lean_inc(v_declName_2317_);
v___x_2333_ = l_Lean_versoDocStringFromString(v_declName_2317_, v_docComment_2318_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v_toVersoDocString_2335_; lean_object* v_deferredChecks_2336_; lean_object* v___x_2337_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_toVersoDocString_2335_ = lean_ctor_get(v_a_2334_, 0);
lean_inc_ref(v_toVersoDocString_2335_);
v_deferredChecks_2336_ = lean_ctor_get(v_a_2334_, 1);
lean_inc_ref(v_deferredChecks_2336_);
lean_dec(v_a_2334_);
v___x_2337_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2317_, v_toVersoDocString_2335_, v_deferredChecks_2336_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec_ref(v_deferredChecks_2336_);
return v___x_2337_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_declName_2317_);
v_a_2338_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2333_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2333_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2365_, lean_object* v_docComment_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_addVersoDocStringFromString(v_declName_2365_, v_docComment_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2375_, lean_object* v_msgData_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v___x_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = 2;
v___x_2383_ = 0;
v___x_2384_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2375_, v_msgData_2376_, v___x_2382_, v___x_2383_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2385_, lean_object* v_msgData_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2385_, v_msgData_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_ref_2385_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2393_, lean_object* v_str_2394_, lean_object* v_as_2395_, size_t v_sz_2396_, size_t v_i_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_a_2407_; uint8_t v___x_2411_; 
v___x_2411_ = lean_usize_dec_lt(v_i_2397_, v_sz_2396_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_b_2398_);
return v___x_2412_;
}
else
{
lean_object* v_a_2413_; lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v_start_2416_; lean_object* v_stop_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2437_; 
v_a_2413_ = lean_array_uget_borrowed(v_as_2395_, v_i_2397_);
v_fst_2414_ = lean_ctor_get(v_a_2413_, 0);
lean_inc(v_fst_2414_);
v_snd_2415_ = lean_ctor_get(v_a_2413_, 1);
v_start_2416_ = lean_ctor_get(v_fst_2414_, 0);
v_stop_2417_ = lean_ctor_get(v_fst_2414_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_fst_2414_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2419_ = v_fst_2414_;
v_isShared_2420_ = v_isSharedCheck_2437_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_stop_2417_);
lean_inc(v_start_2416_);
lean_dec(v_fst_2414_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2437_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_box(0);
if (lean_obj_tag(v___y_2393_) == 1)
{
lean_object* v_val_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v_val_2422_ = lean_ctor_get(v___y_2393_, 0);
v___x_2423_ = lean_nat_add(v_val_2422_, v_start_2416_);
v___x_2424_ = lean_nat_add(v_val_2422_, v_stop_2417_);
v___x_2425_ = 0;
v___x_2426_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2426_, 0, v___x_2423_);
lean_ctor_set(v___x_2426_, 1, v___x_2424_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*2, v___x_2425_);
v___x_2427_ = lean_string_utf8_extract(v_str_2394_, v_start_2416_, v_stop_2417_);
lean_dec(v_stop_2417_);
lean_dec(v_start_2416_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set_tag(v___x_2419_, 2);
lean_ctor_set(v___x_2419_, 1, v___x_2427_);
lean_ctor_set(v___x_2419_, 0, v___x_2426_);
v___x_2429_ = v___x_2419_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_inc(v_snd_2415_);
v___x_2430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_snd_2415_);
v___x_2431_ = l_Lean_MessageData_ofFormat(v___x_2430_);
v___x_2432_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2429_, v___x_2431_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec_ref(v___x_2429_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_dec_ref_known(v___x_2432_, 1);
v_a_2407_ = v___x_2421_;
goto v___jp_2406_;
}
else
{
return v___x_2432_;
}
}
}
else
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
lean_del_object(v___x_2419_);
lean_dec(v_stop_2417_);
lean_dec(v_start_2416_);
lean_inc(v_snd_2415_);
v___x_2434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_snd_2415_);
v___x_2435_ = l_Lean_MessageData_ofFormat(v___x_2434_);
v___x_2436_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2435_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_dec_ref_known(v___x_2436_, 1);
v_a_2407_ = v___x_2421_;
goto v___jp_2406_;
}
else
{
return v___x_2436_;
}
}
}
}
v___jp_2406_:
{
size_t v___x_2408_; size_t v___x_2409_; 
v___x_2408_ = ((size_t)1ULL);
v___x_2409_ = lean_usize_add(v_i_2397_, v___x_2408_);
v_i_2397_ = v___x_2409_;
v_b_2398_ = v_a_2407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2438_, lean_object* v_str_2439_, lean_object* v_as_2440_, lean_object* v_sz_2441_, lean_object* v_i_2442_, lean_object* v_b_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
size_t v_sz_boxed_2451_; size_t v_i_boxed_2452_; lean_object* v_res_2453_; 
v_sz_boxed_2451_ = lean_unbox_usize(v_sz_2441_);
lean_dec(v_sz_2441_);
v_i_boxed_2452_ = lean_unbox_usize(v_i_2442_);
lean_dec(v_i_2442_);
v_res_2453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2438_, v_str_2439_, v_as_2440_, v_sz_boxed_2451_, v_i_boxed_2452_, v_b_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v_as_2440_);
lean_dec_ref(v_str_2439_);
lean_dec(v___y_2438_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_str_2462_; lean_object* v___y_2464_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_str_2462_ = l_Lean_TSyntax_getDocString(v_docstring_2454_);
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = l_Lean_Syntax_getArg(v_docstring_2454_, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2480_);
lean_dec(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_box(0);
v___y_2464_ = v___x_2482_;
goto v___jp_2463_;
}
else
{
lean_object* v_val_2483_; uint8_t v___x_2484_; lean_object* v___x_2485_; 
v_val_2483_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2483_);
lean_dec_ref_known(v___x_2481_, 1);
v___x_2484_ = 0;
v___x_2485_ = l_Lean_SourceInfo_getPos_x3f(v_val_2483_, v___x_2484_);
lean_dec(v_val_2483_);
v___y_2464_ = v___x_2485_;
goto v___jp_2463_;
}
v___jp_2463_:
{
lean_object* v___x_2465_; lean_object* v_fst_2466_; lean_object* v___x_2467_; size_t v_sz_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
lean_inc_ref(v_str_2462_);
v___x_2465_ = l_Lean_rewriteManualLinksCore(v_str_2462_);
v_fst_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_fst_2466_);
lean_dec_ref(v___x_2465_);
v___x_2467_ = lean_box(0);
v_sz_2468_ = lean_array_size(v_fst_2466_);
v___x_2469_ = ((size_t)0ULL);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2464_, v_str_2462_, v_fst_2466_, v_sz_2468_, v___x_2469_, v___x_2467_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v_fst_2466_);
lean_dec_ref(v_str_2462_);
lean_dec(v___y_2464_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v___x_2470_, 0);
lean_dec(v_unused_2478_);
v___x_2472_ = v___x_2470_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v___x_2470_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2467_);
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2467_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v_docstring_2486_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2495_, lean_object* v_msg_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_toCold_2504_; lean_object* v_currRecDepth_2505_; lean_object* v_ref_2506_; uint8_t v_diag_2507_; uint8_t v_suppressElabErrors_2508_; lean_object* v_ref_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_toCold_2504_ = lean_ctor_get(v___y_2501_, 0);
v_currRecDepth_2505_ = lean_ctor_get(v___y_2501_, 1);
v_ref_2506_ = lean_ctor_get(v___y_2501_, 2);
v_diag_2507_ = lean_ctor_get_uint8(v___y_2501_, sizeof(void*)*3);
v_suppressElabErrors_2508_ = lean_ctor_get_uint8(v___y_2501_, sizeof(void*)*3 + 1);
v_ref_2509_ = l_Lean_replaceRef(v_ref_2495_, v_ref_2506_);
lean_inc(v_currRecDepth_2505_);
lean_inc_ref(v_toCold_2504_);
v___x_2510_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2510_, 0, v_toCold_2504_);
lean_ctor_set(v___x_2510_, 1, v_currRecDepth_2505_);
lean_ctor_set(v___x_2510_, 2, v_ref_2509_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*3, v_diag_2507_);
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*3 + 1, v_suppressElabErrors_2508_);
v___x_2511_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___x_2510_, v___y_2502_);
lean_dec_ref_known(v___x_2510_, 3);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2512_, lean_object* v_msg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2512_, v_msg_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec(v_ref_2512_);
return v_res_2521_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2524_ = l_Lean_stringToMessageData(v___x_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_unsigned_to_nat(1u);
v___x_2541_ = l_Lean_Syntax_getArg(v_stx_2526_, v___x_2540_);
if (lean_obj_tag(v___x_2541_) == 1)
{
lean_object* v_kind_2542_; 
v_kind_2542_ = lean_ctor_get(v___x_2541_, 1);
lean_inc(v_kind_2542_);
if (lean_obj_tag(v_kind_2542_) == 1)
{
lean_object* v_pre_2543_; 
v_pre_2543_ = lean_ctor_get(v_kind_2542_, 0);
lean_inc(v_pre_2543_);
if (lean_obj_tag(v_pre_2543_) == 1)
{
lean_object* v_pre_2544_; 
v_pre_2544_ = lean_ctor_get(v_pre_2543_, 0);
lean_inc(v_pre_2544_);
if (lean_obj_tag(v_pre_2544_) == 1)
{
lean_object* v_pre_2545_; 
v_pre_2545_ = lean_ctor_get(v_pre_2544_, 0);
lean_inc(v_pre_2545_);
if (lean_obj_tag(v_pre_2545_) == 1)
{
lean_object* v_pre_2546_; 
v_pre_2546_ = lean_ctor_get(v_pre_2545_, 0);
if (lean_obj_tag(v_pre_2546_) == 0)
{
lean_object* v_args_2547_; lean_object* v_str_2548_; lean_object* v_str_2549_; lean_object* v_str_2550_; lean_object* v_str_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_args_2547_ = lean_ctor_get(v___x_2541_, 2);
lean_inc_ref(v_args_2547_);
lean_dec_ref_known(v___x_2541_, 3);
v_str_2548_ = lean_ctor_get(v_kind_2542_, 1);
lean_inc_ref(v_str_2548_);
lean_dec_ref_known(v_kind_2542_, 2);
v_str_2549_ = lean_ctor_get(v_pre_2543_, 1);
lean_inc_ref(v_str_2549_);
lean_dec_ref_known(v_pre_2543_, 2);
v_str_2550_ = lean_ctor_get(v_pre_2544_, 1);
lean_inc_ref(v_str_2550_);
lean_dec_ref_known(v_pre_2544_, 2);
v_str_2551_ = lean_ctor_get(v_pre_2545_, 1);
lean_inc_ref(v_str_2551_);
lean_dec_ref_known(v_pre_2545_, 2);
v___x_2552_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2553_ = lean_string_dec_eq(v_str_2551_, v___x_2552_);
lean_dec_ref(v_str_2551_);
if (v___x_2553_ == 0)
{
lean_dec_ref(v_str_2550_);
lean_dec_ref(v_str_2549_);
lean_dec_ref(v_str_2548_);
lean_dec_ref(v_args_2547_);
goto v___jp_2534_;
}
else
{
lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2555_ = lean_string_dec_eq(v_str_2550_, v___x_2554_);
lean_dec_ref(v_str_2550_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v_str_2549_);
lean_dec_ref(v_str_2548_);
lean_dec_ref(v_args_2547_);
goto v___jp_2534_;
}
else
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2557_ = lean_string_dec_eq(v_str_2549_, v___x_2556_);
lean_dec_ref(v_str_2549_);
if (v___x_2557_ == 0)
{
lean_dec_ref(v_str_2548_);
lean_dec_ref(v_args_2547_);
goto v___jp_2534_;
}
else
{
lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2558_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2559_ = lean_string_dec_eq(v_str_2548_, v___x_2558_);
lean_dec_ref(v_str_2548_);
if (v___x_2559_ == 0)
{
lean_dec_ref(v_args_2547_);
goto v___jp_2534_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2560_ = lean_array_get_size(v_args_2547_);
v___x_2561_ = lean_unsigned_to_nat(2u);
v___x_2562_ = lean_nat_dec_eq(v___x_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
lean_dec_ref(v_args_2547_);
goto v___jp_2534_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_unsigned_to_nat(0u);
v___x_2564_ = lean_array_fget(v_args_2547_, v___x_2563_);
lean_dec_ref(v_args_2547_);
if (lean_obj_tag(v___x_2564_) == 2)
{
lean_object* v_val_2565_; lean_object* v___x_2566_; 
lean_dec(v_stx_2526_);
v_val_2565_ = lean_ctor_get(v___x_2564_, 1);
lean_inc_ref(v_val_2565_);
lean_dec_ref_known(v___x_2564_, 2);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_val_2565_);
return v___x_2566_;
}
else
{
lean_dec(v___x_2564_);
goto v___jp_2534_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2545_, 2);
lean_dec_ref_known(v_pre_2544_, 2);
lean_dec_ref_known(v_pre_2543_, 2);
lean_dec_ref_known(v_kind_2542_, 2);
lean_dec_ref_known(v___x_2541_, 3);
goto v___jp_2534_;
}
}
else
{
lean_dec_ref_known(v_pre_2544_, 2);
lean_dec(v_pre_2545_);
lean_dec_ref_known(v_pre_2543_, 2);
lean_dec_ref_known(v_kind_2542_, 2);
lean_dec_ref_known(v___x_2541_, 3);
goto v___jp_2534_;
}
}
else
{
lean_dec(v_pre_2544_);
lean_dec_ref_known(v_pre_2543_, 2);
lean_dec_ref_known(v_kind_2542_, 2);
lean_dec_ref_known(v___x_2541_, 3);
goto v___jp_2534_;
}
}
else
{
lean_dec_ref_known(v_kind_2542_, 2);
lean_dec(v_pre_2543_);
lean_dec_ref_known(v___x_2541_, 3);
goto v___jp_2534_;
}
}
else
{
lean_dec(v_kind_2542_);
lean_dec_ref_known(v___x_2541_, 3);
goto v___jp_2534_;
}
}
else
{
lean_dec(v___x_2541_);
goto v___jp_2534_;
}
v___jp_2534_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2535_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2526_);
v___x_2536_ = l_Lean_MessageData_ofSyntax(v_stx_2526_);
v___x_2537_ = l_Lean_indentD(v___x_2536_);
v___x_2538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2535_);
lean_ctor_set(v___x_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2526_, v___x_2538_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v_stx_2526_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2576_, lean_object* v_docComment_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_Name_isAnonymous(v_declName_2576_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_st_ref_get(v___y_2583_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2651_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2650_, v_declName_2576_);
lean_dec_ref(v_env_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
v___y_2586_ = v___y_2578_;
v___y_2587_ = v___y_2579_;
v___y_2588_ = v___y_2580_;
v___y_2589_ = v___y_2581_;
v___y_2590_ = v___y_2582_;
v___y_2591_ = v___y_2583_;
goto v___jp_2585_;
}
else
{
lean_dec_ref_known(v___x_2651_, 1);
if (v___x_2648_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec(v_docComment_2577_);
v___x_2652_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2653_ = l_Lean_MessageData_ofConstName(v_declName_2576_, v___x_2648_);
v___x_2654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2654_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2656_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2657_;
}
else
{
v___y_2586_ = v___y_2578_;
v___y_2587_ = v___y_2579_;
v___y_2588_ = v___y_2580_;
v___y_2589_ = v___y_2581_;
v___y_2590_ = v___y_2582_;
v___y_2591_ = v___y_2583_;
goto v___jp_2585_;
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec(v_docComment_2577_);
lean_dec(v_declName_2576_);
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
v___jp_2585_:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2577_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref_known(v___x_2592_, 1);
v___x_2593_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2577_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2639_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2639_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v_env_2599_; lean_object* v_nextMacroScope_2600_; lean_object* v_ngen_2601_; lean_object* v_auxDeclNGen_2602_; lean_object* v_traceState_2603_; lean_object* v_messages_2604_; lean_object* v_infoState_2605_; lean_object* v_snapshotTasks_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2637_; 
v___x_2598_ = lean_st_ref_take(v___y_2591_);
v_env_2599_ = lean_ctor_get(v___x_2598_, 0);
v_nextMacroScope_2600_ = lean_ctor_get(v___x_2598_, 1);
v_ngen_2601_ = lean_ctor_get(v___x_2598_, 2);
v_auxDeclNGen_2602_ = lean_ctor_get(v___x_2598_, 3);
v_traceState_2603_ = lean_ctor_get(v___x_2598_, 4);
v_messages_2604_ = lean_ctor_get(v___x_2598_, 6);
v_infoState_2605_ = lean_ctor_get(v___x_2598_, 7);
v_snapshotTasks_2606_ = lean_ctor_get(v___x_2598_, 8);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2598_, 5);
lean_dec(v_unused_2638_);
v___x_2608_ = v___x_2598_;
v_isShared_2609_ = v_isSharedCheck_2637_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_snapshotTasks_2606_);
lean_inc(v_infoState_2605_);
lean_inc(v_messages_2604_);
lean_inc(v_traceState_2603_);
lean_inc(v_auxDeclNGen_2602_);
lean_inc(v_ngen_2601_);
lean_inc(v_nextMacroScope_2600_);
lean_inc(v_env_2599_);
lean_dec(v___x_2598_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2637_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2610_ = l_Lean_docStringExt;
v___x_2611_ = l_String_removeLeadingSpaces(v_a_2594_);
v___x_2612_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2610_, v_env_2599_, v_declName_2576_, v___x_2611_);
v___x_2613_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 5, v___x_2613_);
lean_ctor_set(v___x_2608_, 0, v___x_2612_);
v___x_2615_ = v___x_2608_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_nextMacroScope_2600_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_ngen_2601_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v_auxDeclNGen_2602_);
lean_ctor_set(v_reuseFailAlloc_2636_, 4, v_traceState_2603_);
lean_ctor_set(v_reuseFailAlloc_2636_, 5, v___x_2613_);
lean_ctor_set(v_reuseFailAlloc_2636_, 6, v_messages_2604_);
lean_ctor_set(v_reuseFailAlloc_2636_, 7, v_infoState_2605_);
lean_ctor_set(v_reuseFailAlloc_2636_, 8, v_snapshotTasks_2606_);
v___x_2615_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_mctx_2618_; lean_object* v_zetaDeltaFVarIds_2619_; lean_object* v_postponed_2620_; lean_object* v_diag_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2634_; 
v___x_2616_ = lean_st_ref_put(v___y_2591_, v___x_2615_);
v___x_2617_ = lean_st_ref_take(v___y_2589_);
v_mctx_2618_ = lean_ctor_get(v___x_2617_, 0);
v_zetaDeltaFVarIds_2619_ = lean_ctor_get(v___x_2617_, 2);
v_postponed_2620_ = lean_ctor_get(v___x_2617_, 3);
v_diag_2621_ = lean_ctor_get(v___x_2617_, 4);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v___x_2617_, 1);
lean_dec(v_unused_2635_);
v___x_2623_ = v___x_2617_;
v_isShared_2624_ = v_isSharedCheck_2634_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_diag_2621_);
lean_inc(v_postponed_2620_);
lean_inc(v_zetaDeltaFVarIds_2619_);
lean_inc(v_mctx_2618_);
lean_dec(v___x_2617_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2634_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v___x_2626_);
v___x_2628_ = v___x_2623_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_mctx_2618_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_zetaDeltaFVarIds_2619_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v_postponed_2620_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v_diag_2621_);
v___x_2628_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2629_ = lean_st_ref_put(v___y_2589_, v___x_2628_);
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2625_);
v___x_2631_ = v___x_2596_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2625_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_declName_2576_);
v_a_2640_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2593_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2593_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
else
{
lean_dec(v_docComment_2577_);
lean_dec(v_declName_2576_);
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2660_, lean_object* v_docComment_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2660_, v_docComment_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2670_, lean_object* v_declName_2671_, lean_object* v_binders_2672_, lean_object* v_docComment_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
if (v_isVerso_2670_ == 0)
{
lean_object* v___x_2681_; 
lean_dec(v_binders_2672_);
v___x_2681_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2671_, v_docComment_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2681_;
}
else
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_addVersoDocString(v_declName_2671_, v_binders_2672_, v_docComment_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
lean_dec(v_docComment_2673_);
return v___x_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2683_, lean_object* v_declName_2684_, lean_object* v_binders_2685_, lean_object* v_docComment_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
uint8_t v_isVerso_boxed_2694_; lean_object* v_res_2695_; 
v_isVerso_boxed_2694_ = lean_unbox(v_isVerso_2683_);
v_res_2695_ = l_Lean_addDocStringOf(v_isVerso_boxed_2694_, v_declName_2684_, v_binders_2685_, v_docComment_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2696_, lean_object* v_msgData_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2696_, v_msgData_2697_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2706_, lean_object* v_msgData_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2706_, v_msgData_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v_ref_2706_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2716_, lean_object* v_ref_2717_, lean_object* v_msg_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2717_, v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_ref_2728_, lean_object* v_msg_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2727_, v_ref_2728_, v_msg_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_ref_2728_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2738_, lean_object* v_t_2739_){
_start:
{
if (lean_obj_tag(v_t_2739_) == 0)
{
lean_object* v_k_2740_; lean_object* v_v_2741_; lean_object* v_l_2742_; lean_object* v_r_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_3397_; 
v_k_2740_ = lean_ctor_get(v_t_2739_, 1);
v_v_2741_ = lean_ctor_get(v_t_2739_, 2);
v_l_2742_ = lean_ctor_get(v_t_2739_, 3);
v_r_2743_ = lean_ctor_get(v_t_2739_, 4);
v_isSharedCheck_3397_ = !lean_is_exclusive(v_t_2739_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v_t_2739_, 0);
lean_dec(v_unused_3398_);
v___x_2745_ = v_t_2739_;
v_isShared_2746_ = v_isSharedCheck_3397_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_r_2743_);
lean_inc(v_l_2742_);
lean_inc(v_v_2741_);
lean_inc(v_k_2740_);
lean_dec(v_t_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_3397_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___x_2747_; 
v___x_2747_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2738_, v_k_2740_);
switch(v___x_2747_)
{
case 0:
{
lean_object* v_impl_2748_; lean_object* v___x_2749_; 
v_impl_2748_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2738_, v_l_2742_);
v___x_2749_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2748_) == 0)
{
if (lean_obj_tag(v_r_2743_) == 0)
{
lean_object* v_size_2750_; lean_object* v_size_2751_; lean_object* v_k_2752_; lean_object* v_v_2753_; lean_object* v_l_2754_; lean_object* v_r_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v_size_2750_ = lean_ctor_get(v_impl_2748_, 0);
lean_inc(v_size_2750_);
v_size_2751_ = lean_ctor_get(v_r_2743_, 0);
v_k_2752_ = lean_ctor_get(v_r_2743_, 1);
v_v_2753_ = lean_ctor_get(v_r_2743_, 2);
v_l_2754_ = lean_ctor_get(v_r_2743_, 3);
lean_inc(v_l_2754_);
v_r_2755_ = lean_ctor_get(v_r_2743_, 4);
v___x_2756_ = lean_unsigned_to_nat(3u);
v___x_2757_ = lean_nat_mul(v___x_2756_, v_size_2750_);
v___x_2758_ = lean_nat_dec_lt(v___x_2757_, v_size_2751_);
lean_dec(v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2762_; 
lean_dec(v_l_2754_);
v___x_2759_ = lean_nat_add(v___x_2749_, v_size_2750_);
lean_dec(v_size_2750_);
v___x_2760_ = lean_nat_add(v___x_2759_, v_size_2751_);
lean_dec(v___x_2759_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_impl_2748_);
lean_ctor_set(v___x_2745_, 0, v___x_2760_);
v___x_2762_ = v___x_2745_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2763_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2763_, 4, v_r_2743_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
else
{
lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2827_; 
lean_inc(v_r_2755_);
lean_inc(v_v_2753_);
lean_inc(v_k_2752_);
lean_inc(v_size_2751_);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; lean_object* v_unused_2830_; lean_object* v_unused_2831_; lean_object* v_unused_2832_; 
v_unused_2828_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_2829_);
v_unused_2830_ = lean_ctor_get(v_r_2743_, 2);
lean_dec(v_unused_2830_);
v_unused_2831_ = lean_ctor_get(v_r_2743_, 1);
lean_dec(v_unused_2831_);
v_unused_2832_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_2832_);
v___x_2765_ = v_r_2743_;
v_isShared_2766_ = v_isSharedCheck_2827_;
goto v_resetjp_2764_;
}
else
{
lean_dec(v_r_2743_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2827_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v_size_2767_; lean_object* v_k_2768_; lean_object* v_v_2769_; lean_object* v_l_2770_; lean_object* v_r_2771_; lean_object* v_size_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v_size_2767_ = lean_ctor_get(v_l_2754_, 0);
v_k_2768_ = lean_ctor_get(v_l_2754_, 1);
v_v_2769_ = lean_ctor_get(v_l_2754_, 2);
v_l_2770_ = lean_ctor_get(v_l_2754_, 3);
v_r_2771_ = lean_ctor_get(v_l_2754_, 4);
v_size_2772_ = lean_ctor_get(v_r_2755_, 0);
v___x_2773_ = lean_unsigned_to_nat(2u);
v___x_2774_ = lean_nat_mul(v___x_2773_, v_size_2772_);
v___x_2775_ = lean_nat_dec_lt(v_size_2767_, v___x_2774_);
lean_dec(v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2803_; 
lean_inc(v_r_2771_);
lean_inc(v_l_2770_);
lean_inc(v_v_2769_);
lean_inc(v_k_2768_);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_l_2754_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; lean_object* v_unused_2805_; lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2804_ = lean_ctor_get(v_l_2754_, 4);
lean_dec(v_unused_2804_);
v_unused_2805_ = lean_ctor_get(v_l_2754_, 3);
lean_dec(v_unused_2805_);
v_unused_2806_ = lean_ctor_get(v_l_2754_, 2);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_l_2754_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_l_2754_, 0);
lean_dec(v_unused_2808_);
v___x_2777_ = v_l_2754_;
v_isShared_2778_ = v_isSharedCheck_2803_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v_l_2754_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2803_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2793_; 
v___x_2779_ = lean_nat_add(v___x_2749_, v_size_2750_);
lean_dec(v_size_2750_);
v___x_2780_ = lean_nat_add(v___x_2779_, v_size_2751_);
lean_dec(v_size_2751_);
if (lean_obj_tag(v_l_2770_) == 0)
{
lean_object* v_size_2801_; 
v_size_2801_ = lean_ctor_get(v_l_2770_, 0);
lean_inc(v_size_2801_);
v___y_2793_ = v_size_2801_;
goto v___jp_2792_;
}
else
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_unsigned_to_nat(0u);
v___y_2793_ = v___x_2802_;
goto v___jp_2792_;
}
v___jp_2781_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_nat_add(v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 4, v_r_2755_);
lean_ctor_set(v___x_2777_, 3, v_r_2771_);
lean_ctor_set(v___x_2777_, 2, v_v_2753_);
lean_ctor_set(v___x_2777_, 1, v_k_2752_);
lean_ctor_set(v___x_2777_, 0, v___x_2785_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_r_2771_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_r_2755_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v___x_2787_);
lean_ctor_set(v___x_2765_, 3, v___y_2782_);
lean_ctor_set(v___x_2765_, 2, v_v_2769_);
lean_ctor_set(v___x_2765_, 1, v_k_2768_);
lean_ctor_set(v___x_2765_, 0, v___x_2780_);
v___x_2789_ = v___x_2765_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_k_2768_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_v_2769_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v___y_2782_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
v___jp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = lean_nat_add(v___x_2779_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec(v___x_2779_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_l_2770_);
lean_ctor_set(v___x_2745_, 3, v_impl_2748_);
lean_ctor_set(v___x_2745_, 0, v___x_2794_);
v___x_2796_ = v___x_2745_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v_l_2770_);
v___x_2796_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_nat_add(v___x_2749_, v_size_2772_);
if (lean_obj_tag(v_r_2771_) == 0)
{
lean_object* v_size_2798_; 
v_size_2798_ = lean_ctor_get(v_r_2771_, 0);
lean_inc(v_size_2798_);
v___y_2782_ = v___x_2796_;
v___y_2783_ = v___x_2797_;
v___y_2784_ = v_size_2798_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2799_; 
v___x_2799_ = lean_unsigned_to_nat(0u);
v___y_2782_ = v___x_2796_;
v___y_2783_ = v___x_2797_;
v___y_2784_ = v___x_2799_;
goto v___jp_2781_;
}
}
}
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_del_object(v___x_2745_);
v___x_2809_ = lean_nat_add(v___x_2749_, v_size_2750_);
lean_dec(v_size_2750_);
v___x_2810_ = lean_nat_add(v___x_2809_, v_size_2751_);
lean_dec(v_size_2751_);
v___x_2811_ = lean_nat_add(v___x_2809_, v_size_2767_);
lean_dec(v___x_2809_);
lean_inc_ref(v_impl_2748_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 4, v_l_2754_);
lean_ctor_set(v___x_2765_, 3, v_impl_2748_);
lean_ctor_set(v___x_2765_, 2, v_v_2741_);
lean_ctor_set(v___x_2765_, 1, v_k_2740_);
lean_ctor_set(v___x_2765_, 0, v___x_2811_);
v___x_2813_ = v___x_2765_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_l_2754_);
v___x_2813_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_isSharedCheck_2820_ = !lean_is_exclusive(v_impl_2748_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; lean_object* v_unused_2822_; lean_object* v_unused_2823_; lean_object* v_unused_2824_; lean_object* v_unused_2825_; 
v_unused_2821_ = lean_ctor_get(v_impl_2748_, 4);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_impl_2748_, 3);
lean_dec(v_unused_2822_);
v_unused_2823_ = lean_ctor_get(v_impl_2748_, 2);
lean_dec(v_unused_2823_);
v_unused_2824_ = lean_ctor_get(v_impl_2748_, 1);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_impl_2748_, 0);
lean_dec(v_unused_2825_);
v___x_2815_ = v_impl_2748_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_impl_2748_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 4, v_r_2755_);
lean_ctor_set(v___x_2815_, 3, v___x_2813_);
lean_ctor_set(v___x_2815_, 2, v_v_2753_);
lean_ctor_set(v___x_2815_, 1, v_k_2752_);
lean_ctor_set(v___x_2815_, 0, v___x_2810_);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2810_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_k_2752_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_v_2753_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v_r_2755_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2833_; lean_object* v___x_2834_; lean_object* v___x_2836_; 
v_size_2833_ = lean_ctor_get(v_impl_2748_, 0);
lean_inc(v_size_2833_);
v___x_2834_ = lean_nat_add(v___x_2749_, v_size_2833_);
lean_dec(v_size_2833_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_impl_2748_);
lean_ctor_set(v___x_2745_, 0, v___x_2834_);
v___x_2836_ = v___x_2745_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2837_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2837_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2837_, 4, v_r_2743_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
else
{
if (lean_obj_tag(v_r_2743_) == 0)
{
lean_object* v_l_2838_; 
v_l_2838_ = lean_ctor_get(v_r_2743_, 3);
lean_inc(v_l_2838_);
if (lean_obj_tag(v_l_2838_) == 0)
{
lean_object* v_r_2839_; 
v_r_2839_ = lean_ctor_get(v_r_2743_, 4);
lean_inc(v_r_2839_);
if (lean_obj_tag(v_r_2839_) == 0)
{
lean_object* v_size_2840_; lean_object* v_k_2841_; lean_object* v_v_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2855_; 
v_size_2840_ = lean_ctor_get(v_r_2743_, 0);
v_k_2841_ = lean_ctor_get(v_r_2743_, 1);
v_v_2842_ = lean_ctor_get(v_r_2743_, 2);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; lean_object* v_unused_2857_; 
v_unused_2856_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_2856_);
v_unused_2857_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_2857_);
v___x_2844_ = v_r_2743_;
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_v_2842_);
lean_inc(v_k_2841_);
lean_inc(v_size_2840_);
lean_dec(v_r_2743_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_size_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v_size_2846_ = lean_ctor_get(v_l_2838_, 0);
v___x_2847_ = lean_nat_add(v___x_2749_, v_size_2840_);
lean_dec(v_size_2840_);
v___x_2848_ = lean_nat_add(v___x_2749_, v_size_2846_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 4, v_l_2838_);
lean_ctor_set(v___x_2844_, 3, v_impl_2748_);
lean_ctor_set(v___x_2844_, 2, v_v_2741_);
lean_ctor_set(v___x_2844_, 1, v_k_2740_);
lean_ctor_set(v___x_2844_, 0, v___x_2848_);
v___x_2850_ = v___x_2844_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_impl_2748_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_l_2838_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2852_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_r_2839_);
lean_ctor_set(v___x_2745_, 3, v___x_2850_);
lean_ctor_set(v___x_2745_, 2, v_v_2842_);
lean_ctor_set(v___x_2745_, 1, v_k_2841_);
lean_ctor_set(v___x_2745_, 0, v___x_2847_);
v___x_2852_ = v___x_2745_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_k_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_v_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_r_2839_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_k_2858_; lean_object* v_v_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2882_; 
v_k_2858_ = lean_ctor_get(v_r_2743_, 1);
v_v_2859_ = lean_ctor_get(v_r_2743_, 2);
v_isSharedCheck_2882_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; lean_object* v_unused_2884_; lean_object* v_unused_2885_; 
v_unused_2883_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_2883_);
v_unused_2884_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_2884_);
v_unused_2885_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_2885_);
v___x_2861_ = v_r_2743_;
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_v_2859_);
lean_inc(v_k_2858_);
lean_dec(v_r_2743_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2882_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_k_2863_; lean_object* v_v_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2878_; 
v_k_2863_ = lean_ctor_get(v_l_2838_, 1);
v_v_2864_ = lean_ctor_get(v_l_2838_, 2);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_l_2838_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; lean_object* v_unused_2880_; lean_object* v_unused_2881_; 
v_unused_2879_ = lean_ctor_get(v_l_2838_, 4);
lean_dec(v_unused_2879_);
v_unused_2880_ = lean_ctor_get(v_l_2838_, 3);
lean_dec(v_unused_2880_);
v_unused_2881_ = lean_ctor_get(v_l_2838_, 0);
lean_dec(v_unused_2881_);
v___x_2866_ = v_l_2838_;
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_v_2864_);
lean_inc(v_k_2863_);
lean_dec(v_l_2838_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2878_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_unsigned_to_nat(3u);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 4, v_r_2839_);
lean_ctor_set(v___x_2866_, 3, v_r_2839_);
lean_ctor_set(v___x_2866_, 2, v_v_2741_);
lean_ctor_set(v___x_2866_, 1, v_k_2740_);
lean_ctor_set(v___x_2866_, 0, v___x_2749_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_r_2839_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_r_2839_);
v___x_2870_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 3, v_r_2839_);
lean_ctor_set(v___x_2861_, 0, v___x_2749_);
v___x_2872_ = v___x_2861_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_k_2858_);
lean_ctor_set(v_reuseFailAlloc_2876_, 2, v_v_2859_);
lean_ctor_set(v_reuseFailAlloc_2876_, 3, v_r_2839_);
lean_ctor_set(v_reuseFailAlloc_2876_, 4, v_r_2839_);
v___x_2872_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_2872_);
lean_ctor_set(v___x_2745_, 3, v___x_2870_);
lean_ctor_set(v___x_2745_, 2, v_v_2864_);
lean_ctor_set(v___x_2745_, 1, v_k_2863_);
lean_ctor_set(v___x_2745_, 0, v___x_2868_);
v___x_2874_ = v___x_2745_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_k_2863_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_v_2864_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2886_; 
v_r_2886_ = lean_ctor_get(v_r_2743_, 4);
lean_inc(v_r_2886_);
if (lean_obj_tag(v_r_2886_) == 0)
{
lean_object* v_k_2887_; lean_object* v_v_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2899_; 
v_k_2887_ = lean_ctor_get(v_r_2743_, 1);
v_v_2888_ = lean_ctor_get(v_r_2743_, 2);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; lean_object* v_unused_2901_; lean_object* v_unused_2902_; 
v_unused_2900_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_2901_);
v_unused_2902_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_2902_);
v___x_2890_ = v_r_2743_;
v_isShared_2891_ = v_isSharedCheck_2899_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_v_2888_);
lean_inc(v_k_2887_);
lean_dec(v_r_2743_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2899_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = lean_unsigned_to_nat(3u);
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 4, v_l_2838_);
lean_ctor_set(v___x_2890_, 2, v_v_2741_);
lean_ctor_set(v___x_2890_, 1, v_k_2740_);
lean_ctor_set(v___x_2890_, 0, v___x_2749_);
v___x_2894_ = v___x_2890_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_l_2838_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_l_2838_);
v___x_2894_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2896_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_r_2886_);
lean_ctor_set(v___x_2745_, 3, v___x_2894_);
lean_ctor_set(v___x_2745_, 2, v_v_2888_);
lean_ctor_set(v___x_2745_, 1, v_k_2887_);
lean_ctor_set(v___x_2745_, 0, v___x_2892_);
v___x_2896_ = v___x_2745_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v_k_2887_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_v_2888_);
lean_ctor_set(v_reuseFailAlloc_2897_, 3, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_2897_, 4, v_r_2886_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
else
{
lean_object* v_size_2903_; lean_object* v_k_2904_; lean_object* v_v_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2916_; 
v_size_2903_ = lean_ctor_get(v_r_2743_, 0);
v_k_2904_ = lean_ctor_get(v_r_2743_, 1);
v_v_2905_ = lean_ctor_get(v_r_2743_, 2);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2917_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_2918_);
v___x_2907_ = v_r_2743_;
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_v_2905_);
lean_inc(v_k_2904_);
lean_inc(v_size_2903_);
lean_dec(v_r_2743_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 3, v_r_2886_);
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_size_2903_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_k_2904_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_v_2905_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_r_2886_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_r_2886_);
v___x_2910_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2911_ = lean_unsigned_to_nat(2u);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_2910_);
lean_ctor_set(v___x_2745_, 3, v_r_2886_);
lean_ctor_set(v___x_2745_, 0, v___x_2911_);
v___x_2913_ = v___x_2745_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_r_2886_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v___x_2910_);
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
else
{
lean_object* v___x_2920_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_r_2743_);
lean_ctor_set(v___x_2745_, 0, v___x_2749_);
v___x_2920_ = v___x_2745_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_2921_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_2921_, 3, v_r_2743_);
lean_ctor_set(v_reuseFailAlloc_2921_, 4, v_r_2743_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2745_);
lean_dec(v_v_2741_);
lean_dec(v_k_2740_);
if (lean_obj_tag(v_l_2742_) == 0)
{
if (lean_obj_tag(v_r_2743_) == 0)
{
lean_object* v_size_2922_; lean_object* v_k_2923_; lean_object* v_v_2924_; lean_object* v_l_2925_; lean_object* v_r_2926_; lean_object* v_size_2927_; lean_object* v_k_2928_; lean_object* v_v_2929_; lean_object* v_l_2930_; lean_object* v_r_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_size_2922_ = lean_ctor_get(v_l_2742_, 0);
v_k_2923_ = lean_ctor_get(v_l_2742_, 1);
v_v_2924_ = lean_ctor_get(v_l_2742_, 2);
v_l_2925_ = lean_ctor_get(v_l_2742_, 3);
v_r_2926_ = lean_ctor_get(v_l_2742_, 4);
lean_inc(v_r_2926_);
v_size_2927_ = lean_ctor_get(v_r_2743_, 0);
v_k_2928_ = lean_ctor_get(v_r_2743_, 1);
v_v_2929_ = lean_ctor_get(v_r_2743_, 2);
v_l_2930_ = lean_ctor_get(v_r_2743_, 3);
lean_inc(v_l_2930_);
v_r_2931_ = lean_ctor_get(v_r_2743_, 4);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_nat_dec_lt(v_size_2922_, v_size_2927_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3069_; 
lean_inc(v_l_2925_);
lean_inc(v_v_2924_);
lean_inc(v_k_2923_);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; lean_object* v_unused_3071_; lean_object* v_unused_3072_; lean_object* v_unused_3073_; lean_object* v_unused_3074_; 
v_unused_3070_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3070_);
v_unused_3071_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3071_);
v_unused_3072_ = lean_ctor_get(v_l_2742_, 2);
lean_dec(v_unused_3072_);
v_unused_3073_ = lean_ctor_get(v_l_2742_, 1);
lean_dec(v_unused_3073_);
v_unused_3074_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3074_);
v___x_2935_ = v_l_2742_;
v_isShared_2936_ = v_isSharedCheck_3069_;
goto v_resetjp_2934_;
}
else
{
lean_dec(v_l_2742_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3069_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v_tree_2938_; 
v___x_2937_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2923_, v_v_2924_, v_l_2925_, v_r_2926_);
v_tree_2938_ = lean_ctor_get(v___x_2937_, 2);
lean_inc(v_tree_2938_);
if (lean_obj_tag(v_tree_2938_) == 0)
{
lean_object* v_k_2939_; lean_object* v_v_2940_; lean_object* v_size_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v_k_2939_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_k_2939_);
v_v_2940_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_v_2940_);
lean_dec_ref(v___x_2937_);
v_size_2941_ = lean_ctor_get(v_tree_2938_, 0);
v___x_2942_ = lean_unsigned_to_nat(3u);
v___x_2943_ = lean_nat_mul(v___x_2942_, v_size_2941_);
v___x_2944_ = lean_nat_dec_lt(v___x_2943_, v_size_2927_);
lean_dec(v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2948_; 
lean_dec(v_l_2930_);
v___x_2945_ = lean_nat_add(v___x_2932_, v_size_2941_);
v___x_2946_ = lean_nat_add(v___x_2945_, v_size_2927_);
lean_dec(v___x_2945_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_r_2743_);
lean_ctor_set(v___x_2935_, 3, v_tree_2938_);
lean_ctor_set(v___x_2935_, 2, v_v_2940_);
lean_ctor_set(v___x_2935_, 1, v_k_2939_);
lean_ctor_set(v___x_2935_, 0, v___x_2946_);
v___x_2948_ = v___x_2935_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v_k_2939_);
lean_ctor_set(v_reuseFailAlloc_2949_, 2, v_v_2940_);
lean_ctor_set(v_reuseFailAlloc_2949_, 3, v_tree_2938_);
lean_ctor_set(v_reuseFailAlloc_2949_, 4, v_r_2743_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
else
{
lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3004_; 
lean_inc(v_r_2931_);
lean_inc(v_v_2929_);
lean_inc(v_k_2928_);
lean_inc(v_size_2927_);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; lean_object* v_unused_3006_; lean_object* v_unused_3007_; lean_object* v_unused_3008_; lean_object* v_unused_3009_; 
v_unused_3005_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_3005_);
v_unused_3006_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_3006_);
v_unused_3007_ = lean_ctor_get(v_r_2743_, 2);
lean_dec(v_unused_3007_);
v_unused_3008_ = lean_ctor_get(v_r_2743_, 1);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_3009_);
v___x_2951_ = v_r_2743_;
v_isShared_2952_ = v_isSharedCheck_3004_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v_r_2743_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3004_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_size_2953_; lean_object* v_k_2954_; lean_object* v_v_2955_; lean_object* v_l_2956_; lean_object* v_r_2957_; lean_object* v_size_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_size_2953_ = lean_ctor_get(v_l_2930_, 0);
v_k_2954_ = lean_ctor_get(v_l_2930_, 1);
v_v_2955_ = lean_ctor_get(v_l_2930_, 2);
v_l_2956_ = lean_ctor_get(v_l_2930_, 3);
v_r_2957_ = lean_ctor_get(v_l_2930_, 4);
v_size_2958_ = lean_ctor_get(v_r_2931_, 0);
v___x_2959_ = lean_unsigned_to_nat(2u);
v___x_2960_ = lean_nat_mul(v___x_2959_, v_size_2958_);
v___x_2961_ = lean_nat_dec_lt(v_size_2953_, v___x_2960_);
lean_dec(v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2989_; 
lean_inc(v_r_2957_);
lean_inc(v_l_2956_);
lean_inc(v_v_2955_);
lean_inc(v_k_2954_);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_l_2930_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; lean_object* v_unused_2991_; lean_object* v_unused_2992_; lean_object* v_unused_2993_; lean_object* v_unused_2994_; 
v_unused_2990_ = lean_ctor_get(v_l_2930_, 4);
lean_dec(v_unused_2990_);
v_unused_2991_ = lean_ctor_get(v_l_2930_, 3);
lean_dec(v_unused_2991_);
v_unused_2992_ = lean_ctor_get(v_l_2930_, 2);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_l_2930_, 1);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_l_2930_, 0);
lean_dec(v_unused_2994_);
v___x_2963_ = v_l_2930_;
v_isShared_2964_ = v_isSharedCheck_2989_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v_l_2930_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2989_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2979_; 
v___x_2965_ = lean_nat_add(v___x_2932_, v_size_2941_);
v___x_2966_ = lean_nat_add(v___x_2965_, v_size_2927_);
lean_dec(v_size_2927_);
if (lean_obj_tag(v_l_2956_) == 0)
{
lean_object* v_size_2987_; 
v_size_2987_ = lean_ctor_get(v_l_2956_, 0);
lean_inc(v_size_2987_);
v___y_2979_ = v_size_2987_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_unsigned_to_nat(0u);
v___y_2979_ = v___x_2988_;
goto v___jp_2978_;
}
v___jp_2967_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = lean_nat_add(v___y_2968_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec(v___y_2968_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 4, v_r_2931_);
lean_ctor_set(v___x_2963_, 3, v_r_2957_);
lean_ctor_set(v___x_2963_, 2, v_v_2929_);
lean_ctor_set(v___x_2963_, 1, v_k_2928_);
lean_ctor_set(v___x_2963_, 0, v___x_2971_);
v___x_2973_ = v___x_2963_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_r_2957_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_r_2931_);
v___x_2973_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 4, v___x_2973_);
lean_ctor_set(v___x_2951_, 3, v___y_2969_);
lean_ctor_set(v___x_2951_, 2, v_v_2955_);
lean_ctor_set(v___x_2951_, 1, v_k_2954_);
lean_ctor_set(v___x_2951_, 0, v___x_2966_);
v___x_2975_ = v___x_2951_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_k_2954_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_v_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v___y_2969_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
v___jp_2978_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = lean_nat_add(v___x_2965_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec(v___x_2965_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_l_2956_);
lean_ctor_set(v___x_2935_, 3, v_tree_2938_);
lean_ctor_set(v___x_2935_, 2, v_v_2940_);
lean_ctor_set(v___x_2935_, 1, v_k_2939_);
lean_ctor_set(v___x_2935_, 0, v___x_2980_);
v___x_2982_ = v___x_2935_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_k_2939_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_v_2940_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_tree_2938_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_l_2956_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_nat_add(v___x_2932_, v_size_2958_);
if (lean_obj_tag(v_r_2957_) == 0)
{
lean_object* v_size_2984_; 
v_size_2984_ = lean_ctor_get(v_r_2957_, 0);
lean_inc(v_size_2984_);
v___y_2968_ = v___x_2983_;
v___y_2969_ = v___x_2982_;
v___y_2970_ = v_size_2984_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = lean_unsigned_to_nat(0u);
v___y_2968_ = v___x_2983_;
v___y_2969_ = v___x_2982_;
v___y_2970_ = v___x_2985_;
goto v___jp_2967_;
}
}
}
}
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2995_ = lean_nat_add(v___x_2932_, v_size_2941_);
v___x_2996_ = lean_nat_add(v___x_2995_, v_size_2927_);
lean_dec(v_size_2927_);
v___x_2997_ = lean_nat_add(v___x_2995_, v_size_2953_);
lean_dec(v___x_2995_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 4, v_l_2930_);
lean_ctor_set(v___x_2951_, 3, v_tree_2938_);
lean_ctor_set(v___x_2951_, 2, v_v_2940_);
lean_ctor_set(v___x_2951_, 1, v_k_2939_);
lean_ctor_set(v___x_2951_, 0, v___x_2997_);
v___x_2999_ = v___x_2951_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_k_2939_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_v_2940_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_tree_2938_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v_l_2930_);
v___x_2999_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_r_2931_);
lean_ctor_set(v___x_2935_, 3, v___x_2999_);
lean_ctor_set(v___x_2935_, 2, v_v_2929_);
lean_ctor_set(v___x_2935_, 1, v_k_2928_);
lean_ctor_set(v___x_2935_, 0, v___x_2996_);
v___x_3001_ = v___x_2935_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_3002_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_3002_, 3, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3002_, 4, v_r_2931_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
else
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3063_; 
lean_inc(v_r_2931_);
lean_inc(v_v_2929_);
lean_inc(v_k_2928_);
lean_inc(v_size_2927_);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; lean_object* v_unused_3065_; lean_object* v_unused_3066_; lean_object* v_unused_3067_; lean_object* v_unused_3068_; 
v_unused_3064_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_3064_);
v_unused_3065_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v_r_2743_, 2);
lean_dec(v_unused_3066_);
v_unused_3067_ = lean_ctor_get(v_r_2743_, 1);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_3068_);
v___x_3011_ = v_r_2743_;
v_isShared_3012_ = v_isSharedCheck_3063_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v_r_2743_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3063_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
if (lean_obj_tag(v_l_2930_) == 0)
{
if (lean_obj_tag(v_r_2931_) == 0)
{
lean_object* v_k_3013_; lean_object* v_v_3014_; lean_object* v_size_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v_k_3013_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_k_3013_);
v_v_3014_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_v_3014_);
lean_dec_ref(v___x_2937_);
v_size_3015_ = lean_ctor_get(v_l_2930_, 0);
v___x_3016_ = lean_nat_add(v___x_2932_, v_size_2927_);
lean_dec(v_size_2927_);
v___x_3017_ = lean_nat_add(v___x_2932_, v_size_3015_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v_l_2930_);
lean_ctor_set(v___x_3011_, 3, v_tree_2938_);
lean_ctor_set(v___x_3011_, 2, v_v_3014_);
lean_ctor_set(v___x_3011_, 1, v_k_3013_);
lean_ctor_set(v___x_3011_, 0, v___x_3017_);
v___x_3019_ = v___x_3011_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_k_3013_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_v_3014_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_tree_2938_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v_l_2930_);
v___x_3019_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_r_2931_);
lean_ctor_set(v___x_2935_, 3, v___x_3019_);
lean_ctor_set(v___x_2935_, 2, v_v_2929_);
lean_ctor_set(v___x_2935_, 1, v_k_2928_);
lean_ctor_set(v___x_2935_, 0, v___x_3016_);
v___x_3021_ = v___x_2935_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_r_2931_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
else
{
lean_object* v_k_3024_; lean_object* v_v_3025_; lean_object* v_k_3026_; lean_object* v_v_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_size_2927_);
v_k_3024_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_k_3024_);
v_v_3025_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_v_3025_);
lean_dec_ref(v___x_2937_);
v_k_3026_ = lean_ctor_get(v_l_2930_, 1);
v_v_3027_ = lean_ctor_get(v_l_2930_, 2);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_l_2930_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; lean_object* v_unused_3043_; lean_object* v_unused_3044_; 
v_unused_3042_ = lean_ctor_get(v_l_2930_, 4);
lean_dec(v_unused_3042_);
v_unused_3043_ = lean_ctor_get(v_l_2930_, 3);
lean_dec(v_unused_3043_);
v_unused_3044_ = lean_ctor_get(v_l_2930_, 0);
lean_dec(v_unused_3044_);
v___x_3029_ = v_l_2930_;
v_isShared_3030_ = v_isSharedCheck_3041_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_v_3027_);
lean_inc(v_k_3026_);
lean_dec(v_l_2930_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3041_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3031_ = lean_unsigned_to_nat(3u);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 4, v_r_2931_);
lean_ctor_set(v___x_3029_, 3, v_r_2931_);
lean_ctor_set(v___x_3029_, 2, v_v_3025_);
lean_ctor_set(v___x_3029_, 1, v_k_3024_);
lean_ctor_set(v___x_3029_, 0, v___x_2932_);
v___x_3033_ = v___x_3029_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_k_3024_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v_v_3025_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v_r_2931_);
v___x_3033_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3035_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 3, v_r_2931_);
lean_ctor_set(v___x_3011_, 0, v___x_2932_);
v___x_3035_ = v___x_3011_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v_r_2931_);
v___x_3035_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3037_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v___x_3035_);
lean_ctor_set(v___x_2935_, 3, v___x_3033_);
lean_ctor_set(v___x_2935_, 2, v_v_3027_);
lean_ctor_set(v___x_2935_, 1, v_k_3026_);
lean_ctor_set(v___x_2935_, 0, v___x_3031_);
v___x_3037_ = v___x_2935_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_k_3026_);
lean_ctor_set(v_reuseFailAlloc_3038_, 2, v_v_3027_);
lean_ctor_set(v_reuseFailAlloc_3038_, 3, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3038_, 4, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2931_) == 0)
{
lean_object* v_k_3045_; lean_object* v_v_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
lean_dec(v_size_2927_);
v_k_3045_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_k_3045_);
v_v_3046_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_v_3046_);
lean_dec_ref(v___x_2937_);
v___x_3047_ = lean_unsigned_to_nat(3u);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v_l_2930_);
lean_ctor_set(v___x_3011_, 2, v_v_3046_);
lean_ctor_set(v___x_3011_, 1, v_k_3045_);
lean_ctor_set(v___x_3011_, 0, v___x_2932_);
v___x_3049_ = v___x_3011_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_k_3045_);
lean_ctor_set(v_reuseFailAlloc_3053_, 2, v_v_3046_);
lean_ctor_set(v_reuseFailAlloc_3053_, 3, v_l_2930_);
lean_ctor_set(v_reuseFailAlloc_3053_, 4, v_l_2930_);
v___x_3049_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3051_; 
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_r_2931_);
lean_ctor_set(v___x_2935_, 3, v___x_3049_);
lean_ctor_set(v___x_2935_, 2, v_v_2929_);
lean_ctor_set(v___x_2935_, 1, v_k_2928_);
lean_ctor_set(v___x_2935_, 0, v___x_3047_);
v___x_3051_ = v___x_2935_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_3052_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_3052_, 3, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3052_, 4, v_r_2931_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
else
{
lean_object* v_k_3054_; lean_object* v_v_3055_; lean_object* v___x_3057_; 
v_k_3054_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_k_3054_);
v_v_3055_ = lean_ctor_get(v___x_2937_, 1);
lean_inc(v_v_3055_);
lean_dec_ref(v___x_2937_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 3, v_r_2931_);
v___x_3057_ = v___x_3011_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_size_2927_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_3062_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_3062_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_3062_, 4, v_r_2931_);
v___x_3057_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = lean_unsigned_to_nat(2u);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v___x_3057_);
lean_ctor_set(v___x_2935_, 3, v_r_2931_);
lean_ctor_set(v___x_2935_, 2, v_v_3055_);
lean_ctor_set(v___x_2935_, 1, v_k_3054_);
lean_ctor_set(v___x_2935_, 0, v___x_3058_);
v___x_3060_ = v___x_2935_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_k_3054_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v_v_3055_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_r_2931_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v___x_3057_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
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
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3227_; 
lean_inc(v_r_2931_);
lean_inc(v_v_2929_);
lean_inc(v_k_2928_);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_r_2743_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; lean_object* v_unused_3229_; lean_object* v_unused_3230_; lean_object* v_unused_3231_; lean_object* v_unused_3232_; 
v_unused_3228_ = lean_ctor_get(v_r_2743_, 4);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_r_2743_, 3);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_r_2743_, 2);
lean_dec(v_unused_3230_);
v_unused_3231_ = lean_ctor_get(v_r_2743_, 1);
lean_dec(v_unused_3231_);
v_unused_3232_ = lean_ctor_get(v_r_2743_, 0);
lean_dec(v_unused_3232_);
v___x_3076_ = v_r_2743_;
v_isShared_3077_ = v_isSharedCheck_3227_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v_r_2743_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3227_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v_tree_3079_; 
v___x_3078_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2928_, v_v_2929_, v_l_2930_, v_r_2931_);
v_tree_3079_ = lean_ctor_get(v___x_3078_, 2);
lean_inc(v_tree_3079_);
if (lean_obj_tag(v_tree_3079_) == 0)
{
lean_object* v_k_3080_; lean_object* v_v_3081_; lean_object* v_size_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_k_3080_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_k_3080_);
v_v_3081_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_v_3081_);
lean_dec_ref(v___x_3078_);
v_size_3082_ = lean_ctor_get(v_tree_3079_, 0);
v___x_3083_ = lean_unsigned_to_nat(3u);
v___x_3084_ = lean_nat_mul(v___x_3083_, v_size_3082_);
v___x_3085_ = lean_nat_dec_lt(v___x_3084_, v_size_2922_);
lean_dec(v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
lean_dec(v_r_2926_);
v___x_3086_ = lean_nat_add(v___x_2932_, v_size_2922_);
v___x_3087_ = lean_nat_add(v___x_3086_, v_size_3082_);
lean_dec(v___x_3086_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_tree_3079_);
lean_ctor_set(v___x_3076_, 3, v_l_2742_);
lean_ctor_set(v___x_3076_, 2, v_v_3081_);
lean_ctor_set(v___x_3076_, 1, v_k_3080_);
lean_ctor_set(v___x_3076_, 0, v___x_3087_);
v___x_3089_ = v___x_3076_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3090_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3090_, 4, v_tree_3079_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
else
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3156_; 
lean_inc(v_l_2925_);
lean_inc(v_v_2924_);
lean_inc(v_k_2923_);
lean_inc(v_size_2922_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; lean_object* v_unused_3161_; 
v_unused_3157_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_l_2742_, 2);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_l_2742_, 1);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3161_);
v___x_3092_ = v_l_2742_;
v_isShared_3093_ = v_isSharedCheck_3156_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v_l_2742_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3156_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v_size_3094_; lean_object* v_size_3095_; lean_object* v_k_3096_; lean_object* v_v_3097_; lean_object* v_l_3098_; lean_object* v_r_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v_size_3094_ = lean_ctor_get(v_l_2925_, 0);
v_size_3095_ = lean_ctor_get(v_r_2926_, 0);
v_k_3096_ = lean_ctor_get(v_r_2926_, 1);
v_v_3097_ = lean_ctor_get(v_r_2926_, 2);
v_l_3098_ = lean_ctor_get(v_r_2926_, 3);
v_r_3099_ = lean_ctor_get(v_r_2926_, 4);
v___x_3100_ = lean_unsigned_to_nat(2u);
v___x_3101_ = lean_nat_mul(v___x_3100_, v_size_3094_);
v___x_3102_ = lean_nat_dec_lt(v_size_3095_, v___x_3101_);
lean_dec(v___x_3101_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3140_; 
lean_inc(v_r_3099_);
lean_inc(v_l_3098_);
lean_inc(v_v_3097_);
lean_inc(v_k_3096_);
lean_del_object(v___x_3092_);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_r_2926_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; 
v_unused_3141_ = lean_ctor_get(v_r_2926_, 4);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_r_2926_, 3);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_r_2926_, 2);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_r_2926_, 1);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_r_2926_, 0);
lean_dec(v_unused_3145_);
v___x_3104_ = v_r_2926_;
v_isShared_3105_ = v_isSharedCheck_3140_;
goto v_resetjp_3103_;
}
else
{
lean_dec(v_r_2926_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3140_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___x_3128_; lean_object* v___y_3130_; 
v___x_3106_ = lean_nat_add(v___x_2932_, v_size_2922_);
lean_dec(v_size_2922_);
v___x_3107_ = lean_nat_add(v___x_3106_, v_size_3082_);
lean_dec(v___x_3106_);
v___x_3128_ = lean_nat_add(v___x_2932_, v_size_3094_);
if (lean_obj_tag(v_l_3098_) == 0)
{
lean_object* v_size_3138_; 
v_size_3138_ = lean_ctor_get(v_l_3098_, 0);
lean_inc(v_size_3138_);
v___y_3130_ = v_size_3138_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_unsigned_to_nat(0u);
v___y_3130_ = v___x_3139_;
goto v___jp_3129_;
}
v___jp_3108_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = lean_nat_add(v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
lean_inc_ref(v_tree_3079_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 4, v_tree_3079_);
lean_ctor_set(v___x_3104_, 3, v_r_3099_);
lean_ctor_set(v___x_3104_, 2, v_v_3081_);
lean_ctor_set(v___x_3104_, 1, v_k_3080_);
lean_ctor_set(v___x_3104_, 0, v___x_3112_);
v___x_3114_ = v___x_3104_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v_r_3099_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v_tree_3079_);
v___x_3114_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
v_isSharedCheck_3121_ = !lean_is_exclusive(v_tree_3079_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3122_ = lean_ctor_get(v_tree_3079_, 4);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_tree_3079_, 3);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_tree_3079_, 2);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_tree_3079_, 1);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_tree_3079_, 0);
lean_dec(v_unused_3126_);
v___x_3116_ = v_tree_3079_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_dec(v_tree_3079_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 4, v___x_3114_);
lean_ctor_set(v___x_3116_, 3, v___y_3109_);
lean_ctor_set(v___x_3116_, 2, v_v_3097_);
lean_ctor_set(v___x_3116_, 1, v_k_3096_);
lean_ctor_set(v___x_3116_, 0, v___x_3107_);
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_k_3096_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_v_3097_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v___y_3109_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v___x_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
v___jp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3131_ = lean_nat_add(v___x_3128_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec(v___x_3128_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_3098_);
lean_ctor_set(v___x_3076_, 3, v_l_2925_);
lean_ctor_set(v___x_3076_, 2, v_v_2924_);
lean_ctor_set(v___x_3076_, 1, v_k_2923_);
lean_ctor_set(v___x_3076_, 0, v___x_3131_);
v___x_3133_ = v___x_3076_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_k_2923_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_v_2924_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_l_3098_);
v___x_3133_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_nat_add(v___x_2932_, v_size_3082_);
if (lean_obj_tag(v_r_3099_) == 0)
{
lean_object* v_size_3135_; 
v_size_3135_ = lean_ctor_get(v_r_3099_, 0);
lean_inc(v_size_3135_);
v___y_3109_ = v___x_3133_;
v___y_3110_ = v___x_3134_;
v___y_3111_ = v_size_3135_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_unsigned_to_nat(0u);
v___y_3109_ = v___x_3133_;
v___y_3110_ = v___x_3134_;
v___y_3111_ = v___x_3136_;
goto v___jp_3108_;
}
}
}
}
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3146_ = lean_nat_add(v___x_2932_, v_size_2922_);
lean_dec(v_size_2922_);
v___x_3147_ = lean_nat_add(v___x_3146_, v_size_3082_);
lean_dec(v___x_3146_);
v___x_3148_ = lean_nat_add(v___x_2932_, v_size_3082_);
v___x_3149_ = lean_nat_add(v___x_3148_, v_size_3095_);
lean_dec(v___x_3148_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_tree_3079_);
lean_ctor_set(v___x_3076_, 3, v_r_2926_);
lean_ctor_set(v___x_3076_, 2, v_v_3081_);
lean_ctor_set(v___x_3076_, 1, v_k_3080_);
lean_ctor_set(v___x_3076_, 0, v___x_3149_);
v___x_3151_ = v___x_3076_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_k_3080_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v_v_3081_);
lean_ctor_set(v_reuseFailAlloc_3155_, 3, v_r_2926_);
lean_ctor_set(v_reuseFailAlloc_3155_, 4, v_tree_3079_);
v___x_3151_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3153_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v___x_3151_);
lean_ctor_set(v___x_3092_, 0, v___x_3147_);
v___x_3153_ = v___x_3092_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3147_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_k_2923_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_v_2924_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2925_) == 0)
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3185_; 
lean_inc_ref(v_l_2925_);
lean_inc(v_v_2924_);
lean_inc(v_k_2923_);
lean_inc(v_size_2922_);
v_isSharedCheck_3185_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; lean_object* v_unused_3190_; 
v_unused_3186_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_l_2742_, 2);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_l_2742_, 1);
lean_dec(v_unused_3189_);
v_unused_3190_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3190_);
v___x_3163_ = v_l_2742_;
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v_l_2742_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3185_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_r_2926_) == 0)
{
lean_object* v_k_3165_; lean_object* v_v_3166_; lean_object* v_size_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v_k_3165_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_k_3165_);
v_v_3166_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_v_3166_);
lean_dec_ref(v___x_3078_);
v_size_3167_ = lean_ctor_get(v_r_2926_, 0);
v___x_3168_ = lean_nat_add(v___x_2932_, v_size_2922_);
lean_dec(v_size_2922_);
v___x_3169_ = lean_nat_add(v___x_2932_, v_size_3167_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_tree_3079_);
lean_ctor_set(v___x_3076_, 3, v_r_2926_);
lean_ctor_set(v___x_3076_, 2, v_v_3166_);
lean_ctor_set(v___x_3076_, 1, v_k_3165_);
lean_ctor_set(v___x_3076_, 0, v___x_3169_);
v___x_3171_ = v___x_3076_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_k_3165_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_v_3166_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_r_2926_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_tree_3079_);
v___x_3171_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3173_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v___x_3171_);
lean_ctor_set(v___x_3163_, 0, v___x_3168_);
v___x_3173_ = v___x_3163_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_k_2923_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_v_2924_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
else
{
lean_object* v_k_3176_; lean_object* v_v_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_dec(v_size_2922_);
v_k_3176_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_k_3176_);
v_v_3177_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_v_3177_);
lean_dec_ref(v___x_3078_);
v___x_3178_ = lean_unsigned_to_nat(3u);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_r_2926_);
lean_ctor_set(v___x_3076_, 3, v_r_2926_);
lean_ctor_set(v___x_3076_, 2, v_v_3177_);
lean_ctor_set(v___x_3076_, 1, v_k_3176_);
lean_ctor_set(v___x_3076_, 0, v___x_2932_);
v___x_3180_ = v___x_3076_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_k_3176_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_v_3177_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_r_2926_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_r_2926_);
v___x_3180_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3182_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 4, v___x_3180_);
lean_ctor_set(v___x_3163_, 0, v___x_3178_);
v___x_3182_ = v___x_3163_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_k_2923_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_v_2924_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2926_) == 0)
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3215_; 
lean_inc(v_l_2925_);
lean_inc(v_v_2924_);
lean_inc(v_k_2923_);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; lean_object* v_unused_3220_; 
v_unused_3216_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_l_2742_, 2);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_l_2742_, 1);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3220_);
v___x_3192_ = v_l_2742_;
v_isShared_3193_ = v_isSharedCheck_3215_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v_l_2742_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3215_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_k_3194_; lean_object* v_v_3195_; lean_object* v_k_3196_; lean_object* v_v_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3211_; 
v_k_3194_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_k_3194_);
v_v_3195_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_v_3195_);
lean_dec_ref(v___x_3078_);
v_k_3196_ = lean_ctor_get(v_r_2926_, 1);
v_v_3197_ = lean_ctor_get(v_r_2926_, 2);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_r_2926_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; lean_object* v_unused_3213_; lean_object* v_unused_3214_; 
v_unused_3212_ = lean_ctor_get(v_r_2926_, 4);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_r_2926_, 3);
lean_dec(v_unused_3213_);
v_unused_3214_ = lean_ctor_get(v_r_2926_, 0);
lean_dec(v_unused_3214_);
v___x_3199_ = v_r_2926_;
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_v_3197_);
lean_inc(v_k_3196_);
lean_dec(v_r_2926_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3201_ = lean_unsigned_to_nat(3u);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 4, v_l_2925_);
lean_ctor_set(v___x_3199_, 3, v_l_2925_);
lean_ctor_set(v___x_3199_, 2, v_v_2924_);
lean_ctor_set(v___x_3199_, 1, v_k_2923_);
lean_ctor_set(v___x_3199_, 0, v___x_2932_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_k_2923_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v_v_2924_);
lean_ctor_set(v_reuseFailAlloc_3210_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3210_, 4, v_l_2925_);
v___x_3203_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_l_2925_);
lean_ctor_set(v___x_3076_, 3, v_l_2925_);
lean_ctor_set(v___x_3076_, 2, v_v_3195_);
lean_ctor_set(v___x_3076_, 1, v_k_3194_);
lean_ctor_set(v___x_3076_, 0, v___x_2932_);
v___x_3205_ = v___x_3076_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_k_3194_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_v_3195_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_l_2925_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v_l_2925_);
v___x_3205_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 4, v___x_3205_);
lean_ctor_set(v___x_3192_, 3, v___x_3203_);
lean_ctor_set(v___x_3192_, 2, v_v_3197_);
lean_ctor_set(v___x_3192_, 1, v_k_3196_);
lean_ctor_set(v___x_3192_, 0, v___x_3201_);
v___x_3207_ = v___x_3192_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_k_3196_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_v_3197_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v___x_3205_);
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
}
}
else
{
lean_object* v_k_3221_; lean_object* v_v_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v_k_3221_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_k_3221_);
v_v_3222_ = lean_ctor_get(v___x_3078_, 1);
lean_inc(v_v_3222_);
lean_dec_ref(v___x_3078_);
v___x_3223_ = lean_unsigned_to_nat(2u);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 4, v_r_2926_);
lean_ctor_set(v___x_3076_, 3, v_l_2742_);
lean_ctor_set(v___x_3076_, 2, v_v_3222_);
lean_ctor_set(v___x_3076_, 1, v_k_3221_);
lean_ctor_set(v___x_3076_, 0, v___x_3223_);
v___x_3225_ = v___x_3076_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3221_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3222_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_r_2926_);
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
return v_l_2742_;
}
}
else
{
return v_r_2743_;
}
}
default: 
{
lean_object* v_impl_3233_; lean_object* v___x_3234_; 
v_impl_3233_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2738_, v_r_2743_);
v___x_3234_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3233_) == 0)
{
if (lean_obj_tag(v_l_2742_) == 0)
{
lean_object* v_size_3235_; lean_object* v_size_3236_; lean_object* v_k_3237_; lean_object* v_v_3238_; lean_object* v_l_3239_; lean_object* v_r_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v_size_3235_ = lean_ctor_get(v_impl_3233_, 0);
lean_inc(v_size_3235_);
v_size_3236_ = lean_ctor_get(v_l_2742_, 0);
v_k_3237_ = lean_ctor_get(v_l_2742_, 1);
v_v_3238_ = lean_ctor_get(v_l_2742_, 2);
v_l_3239_ = lean_ctor_get(v_l_2742_, 3);
v_r_3240_ = lean_ctor_get(v_l_2742_, 4);
lean_inc(v_r_3240_);
v___x_3241_ = lean_unsigned_to_nat(3u);
v___x_3242_ = lean_nat_mul(v___x_3241_, v_size_3235_);
v___x_3243_ = lean_nat_dec_lt(v___x_3242_, v_size_3236_);
lean_dec(v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec(v_r_3240_);
v___x_3244_ = lean_nat_add(v___x_3234_, v_size_3236_);
v___x_3245_ = lean_nat_add(v___x_3244_, v_size_3235_);
lean_dec(v_size_3235_);
lean_dec(v___x_3244_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_impl_3233_);
lean_ctor_set(v___x_2745_, 0, v___x_3245_);
v___x_3247_ = v___x_2745_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v_impl_3233_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3314_; 
lean_inc(v_l_3239_);
lean_inc(v_v_3238_);
lean_inc(v_k_3237_);
lean_inc(v_size_3236_);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; lean_object* v_unused_3316_; lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; 
v_unused_3315_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3315_);
v_unused_3316_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v_l_2742_, 2);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_l_2742_, 1);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3319_);
v___x_3250_ = v_l_2742_;
v_isShared_3251_ = v_isSharedCheck_3314_;
goto v_resetjp_3249_;
}
else
{
lean_dec(v_l_2742_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3314_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v_size_3252_; lean_object* v_size_3253_; lean_object* v_k_3254_; lean_object* v_v_3255_; lean_object* v_l_3256_; lean_object* v_r_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_size_3252_ = lean_ctor_get(v_l_3239_, 0);
v_size_3253_ = lean_ctor_get(v_r_3240_, 0);
v_k_3254_ = lean_ctor_get(v_r_3240_, 1);
v_v_3255_ = lean_ctor_get(v_r_3240_, 2);
v_l_3256_ = lean_ctor_get(v_r_3240_, 3);
v_r_3257_ = lean_ctor_get(v_r_3240_, 4);
v___x_3258_ = lean_unsigned_to_nat(2u);
v___x_3259_ = lean_nat_mul(v___x_3258_, v_size_3252_);
v___x_3260_ = lean_nat_dec_lt(v_size_3253_, v___x_3259_);
lean_dec(v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3289_; 
lean_inc(v_r_3257_);
lean_inc(v_l_3256_);
lean_inc(v_v_3255_);
lean_inc(v_k_3254_);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_r_3240_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; 
v_unused_3290_ = lean_ctor_get(v_r_3240_, 4);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_r_3240_, 3);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_r_3240_, 2);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_r_3240_, 1);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_r_3240_, 0);
lean_dec(v_unused_3294_);
v___x_3262_ = v_r_3240_;
v_isShared_3263_ = v_isSharedCheck_3289_;
goto v_resetjp_3261_;
}
else
{
lean_dec(v_r_3240_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3289_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___x_3277_; lean_object* v___y_3279_; 
v___x_3264_ = lean_nat_add(v___x_3234_, v_size_3236_);
lean_dec(v_size_3236_);
v___x_3265_ = lean_nat_add(v___x_3264_, v_size_3235_);
lean_dec(v___x_3264_);
v___x_3277_ = lean_nat_add(v___x_3234_, v_size_3252_);
if (lean_obj_tag(v_l_3256_) == 0)
{
lean_object* v_size_3287_; 
v_size_3287_ = lean_ctor_get(v_l_3256_, 0);
lean_inc(v_size_3287_);
v___y_3279_ = v_size_3287_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_unsigned_to_nat(0u);
v___y_3279_ = v___x_3288_;
goto v___jp_3278_;
}
v___jp_3266_:
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = lean_nat_add(v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec(v___y_3268_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 4, v_impl_3233_);
lean_ctor_set(v___x_3262_, 3, v_r_3257_);
lean_ctor_set(v___x_3262_, 2, v_v_2741_);
lean_ctor_set(v___x_3262_, 1, v_k_2740_);
lean_ctor_set(v___x_3262_, 0, v___x_3270_);
v___x_3272_ = v___x_3262_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_r_3257_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_impl_3233_);
v___x_3272_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v___x_3272_);
lean_ctor_set(v___x_3250_, 3, v___y_3267_);
lean_ctor_set(v___x_3250_, 2, v_v_3255_);
lean_ctor_set(v___x_3250_, 1, v_k_3254_);
lean_ctor_set(v___x_3250_, 0, v___x_3265_);
v___x_3274_ = v___x_3250_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3254_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3255_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v___y_3267_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
v___jp_3278_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_nat_add(v___x_3277_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec(v___x_3277_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_l_3256_);
lean_ctor_set(v___x_2745_, 3, v_l_3239_);
lean_ctor_set(v___x_2745_, 2, v_v_3238_);
lean_ctor_set(v___x_2745_, 1, v_k_3237_);
lean_ctor_set(v___x_2745_, 0, v___x_3280_);
v___x_3282_ = v___x_2745_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3237_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3238_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_l_3239_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_l_3256_);
v___x_3282_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_nat_add(v___x_3234_, v_size_3235_);
lean_dec(v_size_3235_);
if (lean_obj_tag(v_r_3257_) == 0)
{
lean_object* v_size_3284_; 
v_size_3284_ = lean_ctor_get(v_r_3257_, 0);
lean_inc(v_size_3284_);
v___y_3267_ = v___x_3282_;
v___y_3268_ = v___x_3283_;
v___y_3269_ = v_size_3284_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___y_3267_ = v___x_3282_;
v___y_3268_ = v___x_3283_;
v___y_3269_ = v___x_3285_;
goto v___jp_3266_;
}
}
}
}
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_del_object(v___x_2745_);
v___x_3295_ = lean_nat_add(v___x_3234_, v_size_3236_);
lean_dec(v_size_3236_);
v___x_3296_ = lean_nat_add(v___x_3295_, v_size_3235_);
lean_dec(v___x_3295_);
v___x_3297_ = lean_nat_add(v___x_3234_, v_size_3235_);
lean_dec(v_size_3235_);
v___x_3298_ = lean_nat_add(v___x_3297_, v_size_3253_);
lean_dec(v___x_3297_);
lean_inc_ref(v_impl_3233_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 4, v_impl_3233_);
lean_ctor_set(v___x_3250_, 3, v_r_3240_);
lean_ctor_set(v___x_3250_, 2, v_v_2741_);
lean_ctor_set(v___x_3250_, 1, v_k_2740_);
lean_ctor_set(v___x_3250_, 0, v___x_3298_);
v___x_3300_ = v___x_3250_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_r_3240_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_impl_3233_);
v___x_3300_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_isSharedCheck_3307_ = !lean_is_exclusive(v_impl_3233_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; 
v_unused_3308_ = lean_ctor_get(v_impl_3233_, 4);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_impl_3233_, 3);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_impl_3233_, 2);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_impl_3233_, 1);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_impl_3233_, 0);
lean_dec(v_unused_3312_);
v___x_3302_ = v_impl_3233_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_dec(v_impl_3233_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 4, v___x_3300_);
lean_ctor_set(v___x_3302_, 3, v_l_3239_);
lean_ctor_set(v___x_3302_, 2, v_v_3238_);
lean_ctor_set(v___x_3302_, 1, v_k_3237_);
lean_ctor_set(v___x_3302_, 0, v___x_3296_);
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_k_3237_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_v_3238_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_l_3239_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v___x_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; 
v_size_3320_ = lean_ctor_get(v_impl_3233_, 0);
lean_inc(v_size_3320_);
v___x_3321_ = lean_nat_add(v___x_3234_, v_size_3320_);
lean_dec(v_size_3320_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_impl_3233_);
lean_ctor_set(v___x_2745_, 0, v___x_3321_);
v___x_3323_ = v___x_2745_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3324_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3324_, 4, v_impl_3233_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
else
{
if (lean_obj_tag(v_l_2742_) == 0)
{
lean_object* v_l_3325_; 
v_l_3325_ = lean_ctor_get(v_l_2742_, 3);
if (lean_obj_tag(v_l_3325_) == 0)
{
lean_object* v_r_3326_; 
lean_inc_ref(v_l_3325_);
v_r_3326_ = lean_ctor_get(v_l_2742_, 4);
lean_inc(v_r_3326_);
if (lean_obj_tag(v_r_3326_) == 0)
{
lean_object* v_size_3327_; lean_object* v_k_3328_; lean_object* v_v_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3342_; 
v_size_3327_ = lean_ctor_get(v_l_2742_, 0);
v_k_3328_ = lean_ctor_get(v_l_2742_, 1);
v_v_3329_ = lean_ctor_get(v_l_2742_, 2);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; lean_object* v_unused_3344_; 
v_unused_3343_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3343_);
v_unused_3344_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3344_);
v___x_3331_ = v_l_2742_;
v_isShared_3332_ = v_isSharedCheck_3342_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_v_3329_);
lean_inc(v_k_3328_);
lean_inc(v_size_3327_);
lean_dec(v_l_2742_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3342_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_size_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v_size_3333_ = lean_ctor_get(v_r_3326_, 0);
v___x_3334_ = lean_nat_add(v___x_3234_, v_size_3327_);
lean_dec(v_size_3327_);
v___x_3335_ = lean_nat_add(v___x_3234_, v_size_3333_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v_impl_3233_);
lean_ctor_set(v___x_3331_, 3, v_r_3326_);
lean_ctor_set(v___x_3331_, 2, v_v_2741_);
lean_ctor_set(v___x_3331_, 1, v_k_2740_);
lean_ctor_set(v___x_3331_, 0, v___x_3335_);
v___x_3337_ = v___x_3331_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_r_3326_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_impl_3233_);
v___x_3337_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3339_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_3337_);
lean_ctor_set(v___x_2745_, 3, v_l_3325_);
lean_ctor_set(v___x_2745_, 2, v_v_3329_);
lean_ctor_set(v___x_2745_, 1, v_k_3328_);
lean_ctor_set(v___x_2745_, 0, v___x_3334_);
v___x_3339_ = v___x_2745_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_l_3325_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v___x_3337_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3357_; 
v_k_3345_ = lean_ctor_get(v_l_2742_, 1);
v_v_3346_ = lean_ctor_get(v_l_2742_, 2);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; lean_object* v_unused_3359_; lean_object* v_unused_3360_; 
v_unused_3358_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3358_);
v_unused_3359_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3359_);
v_unused_3360_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3360_);
v___x_3348_ = v_l_2742_;
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_v_3346_);
lean_inc(v_k_3345_);
lean_dec(v_l_2742_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3350_ = lean_unsigned_to_nat(3u);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 3, v_r_3326_);
lean_ctor_set(v___x_3348_, 2, v_v_2741_);
lean_ctor_set(v___x_3348_, 1, v_k_2740_);
lean_ctor_set(v___x_3348_, 0, v___x_3234_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v_r_3326_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v_r_3326_);
v___x_3352_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3354_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_3352_);
lean_ctor_set(v___x_2745_, 3, v_l_3325_);
lean_ctor_set(v___x_2745_, 2, v_v_3346_);
lean_ctor_set(v___x_2745_, 1, v_k_3345_);
lean_ctor_set(v___x_2745_, 0, v___x_3350_);
v___x_3354_ = v___x_2745_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3345_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3346_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_l_3325_);
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
else
{
lean_object* v_r_3361_; 
v_r_3361_ = lean_ctor_get(v_l_2742_, 4);
lean_inc(v_r_3361_);
if (lean_obj_tag(v_r_3361_) == 0)
{
lean_object* v_k_3362_; lean_object* v_v_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3386_; 
lean_inc(v_l_3325_);
v_k_3362_ = lean_ctor_get(v_l_2742_, 1);
v_v_3363_ = lean_ctor_get(v_l_2742_, 2);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_l_2742_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; lean_object* v_unused_3388_; lean_object* v_unused_3389_; 
v_unused_3387_ = lean_ctor_get(v_l_2742_, 4);
lean_dec(v_unused_3387_);
v_unused_3388_ = lean_ctor_get(v_l_2742_, 3);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_l_2742_, 0);
lean_dec(v_unused_3389_);
v___x_3365_ = v_l_2742_;
v_isShared_3366_ = v_isSharedCheck_3386_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_v_3363_);
lean_inc(v_k_3362_);
lean_dec(v_l_2742_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3386_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_k_3367_; lean_object* v_v_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3382_; 
v_k_3367_ = lean_ctor_get(v_r_3361_, 1);
v_v_3368_ = lean_ctor_get(v_r_3361_, 2);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_r_3361_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3383_ = lean_ctor_get(v_r_3361_, 4);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3361_, 3);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3361_, 0);
lean_dec(v_unused_3385_);
v___x_3370_ = v_r_3361_;
v_isShared_3371_ = v_isSharedCheck_3382_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_v_3368_);
lean_inc(v_k_3367_);
lean_dec(v_r_3361_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3382_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_unsigned_to_nat(3u);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 4, v_l_3325_);
lean_ctor_set(v___x_3370_, 3, v_l_3325_);
lean_ctor_set(v___x_3370_, 2, v_v_3363_);
lean_ctor_set(v___x_3370_, 1, v_k_3362_);
lean_ctor_set(v___x_3370_, 0, v___x_3234_);
v___x_3374_ = v___x_3370_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3362_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3363_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_l_3325_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_l_3325_);
v___x_3374_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3376_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 4, v_l_3325_);
lean_ctor_set(v___x_3365_, 2, v_v_2741_);
lean_ctor_set(v___x_3365_, 1, v_k_2740_);
lean_ctor_set(v___x_3365_, 0, v___x_3234_);
v___x_3376_ = v___x_3365_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3380_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3380_, 3, v_l_3325_);
lean_ctor_set(v_reuseFailAlloc_3380_, 4, v_l_3325_);
v___x_3376_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_3376_);
lean_ctor_set(v___x_2745_, 3, v___x_3374_);
lean_ctor_set(v___x_2745_, 2, v_v_3368_);
lean_ctor_set(v___x_2745_, 1, v_k_3367_);
lean_ctor_set(v___x_2745_, 0, v___x_3372_);
v___x_3378_ = v___x_2745_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3367_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3368_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_unsigned_to_nat(2u);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_r_3361_);
lean_ctor_set(v___x_2745_, 0, v___x_3390_);
v___x_3392_ = v___x_2745_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3393_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3393_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3393_, 4, v_r_3361_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3395_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v_l_2742_);
lean_ctor_set(v___x_2745_, 0, v___x_3234_);
v___x_3395_ = v___x_2745_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_k_2740_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_v_2741_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_l_2742_);
lean_ctor_set(v_reuseFailAlloc_3396_, 4, v_l_2742_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
}
}
else
{
return v_t_2739_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3399_, lean_object* v_t_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3399_, v_t_3400_);
lean_dec(v_k_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3402_, lean_object* v_x_3403_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3402_, v_x_3403_);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3405_, lean_object* v_x_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3405_, v_x_3406_);
lean_dec(v_declName_3405_);
return v_res_3407_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___f_3419_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3463_; lean_object* v_env_3464_; lean_object* v___x_3465_; 
lean_inc(v_declName_3411_);
v___f_3419_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3419_, 0, v_declName_3411_);
v___x_3463_ = lean_st_ref_get(v___y_3417_);
v_env_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc_ref(v_env_3464_);
lean_dec(v___x_3463_);
v___x_3465_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3464_, v_declName_3411_);
lean_dec_ref(v_env_3464_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_dec(v_declName_3411_);
v___y_3421_ = v___y_3415_;
v___y_3422_ = v___y_3417_;
goto v___jp_3420_;
}
else
{
uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; 
lean_dec_ref_known(v___x_3465_, 1);
lean_dec_ref(v___f_3419_);
v___x_3466_ = 0;
v___x_3467_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3468_ = l_Lean_MessageData_ofConstName(v_declName_3411_, v___x_3466_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3471_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3472_;
}
v___jp_3420_:
{
lean_object* v___x_3423_; lean_object* v_env_3424_; lean_object* v_nextMacroScope_3425_; lean_object* v_ngen_3426_; lean_object* v_auxDeclNGen_3427_; lean_object* v_traceState_3428_; lean_object* v_messages_3429_; lean_object* v_infoState_3430_; lean_object* v_snapshotTasks_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3461_; 
v___x_3423_ = lean_st_ref_take(v___y_3422_);
v_env_3424_ = lean_ctor_get(v___x_3423_, 0);
v_nextMacroScope_3425_ = lean_ctor_get(v___x_3423_, 1);
v_ngen_3426_ = lean_ctor_get(v___x_3423_, 2);
v_auxDeclNGen_3427_ = lean_ctor_get(v___x_3423_, 3);
v_traceState_3428_ = lean_ctor_get(v___x_3423_, 4);
v_messages_3429_ = lean_ctor_get(v___x_3423_, 6);
v_infoState_3430_ = lean_ctor_get(v___x_3423_, 7);
v_snapshotTasks_3431_ = lean_ctor_get(v___x_3423_, 8);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3423_, 5);
lean_dec(v_unused_3462_);
v___x_3433_ = v___x_3423_;
v_isShared_3434_ = v_isSharedCheck_3461_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snapshotTasks_3431_);
lean_inc(v_infoState_3430_);
lean_inc(v_messages_3429_);
lean_inc(v_traceState_3428_);
lean_inc(v_auxDeclNGen_3427_);
lean_inc(v_ngen_3426_);
lean_inc(v_nextMacroScope_3425_);
lean_inc(v_env_3424_);
lean_dec(v___x_3423_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3461_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3435_ = l_Lean_docStringExt;
v___x_3436_ = lean_box(2);
v___x_3437_ = lean_box(0);
v___x_3438_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3435_, v_env_3424_, v___f_3419_, v___x_3436_, v___x_3437_);
v___x_3439_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 5, v___x_3439_);
lean_ctor_set(v___x_3433_, 0, v___x_3438_);
v___x_3441_ = v___x_3433_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3438_);
lean_ctor_set(v_reuseFailAlloc_3460_, 1, v_nextMacroScope_3425_);
lean_ctor_set(v_reuseFailAlloc_3460_, 2, v_ngen_3426_);
lean_ctor_set(v_reuseFailAlloc_3460_, 3, v_auxDeclNGen_3427_);
lean_ctor_set(v_reuseFailAlloc_3460_, 4, v_traceState_3428_);
lean_ctor_set(v_reuseFailAlloc_3460_, 5, v___x_3439_);
lean_ctor_set(v_reuseFailAlloc_3460_, 6, v_messages_3429_);
lean_ctor_set(v_reuseFailAlloc_3460_, 7, v_infoState_3430_);
lean_ctor_set(v_reuseFailAlloc_3460_, 8, v_snapshotTasks_3431_);
v___x_3441_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_mctx_3444_; lean_object* v_zetaDeltaFVarIds_3445_; lean_object* v_postponed_3446_; lean_object* v_diag_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3458_; 
v___x_3442_ = lean_st_ref_put(v___y_3422_, v___x_3441_);
v___x_3443_ = lean_st_ref_take(v___y_3421_);
v_mctx_3444_ = lean_ctor_get(v___x_3443_, 0);
v_zetaDeltaFVarIds_3445_ = lean_ctor_get(v___x_3443_, 2);
v_postponed_3446_ = lean_ctor_get(v___x_3443_, 3);
v_diag_3447_ = lean_ctor_get(v___x_3443_, 4);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___x_3443_, 1);
lean_dec(v_unused_3459_);
v___x_3449_ = v___x_3443_;
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_diag_3447_);
lean_inc(v_postponed_3446_);
lean_inc(v_zetaDeltaFVarIds_3445_);
lean_inc(v_mctx_3444_);
lean_dec(v___x_3443_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3458_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v___x_3452_);
v___x_3454_ = v___x_3449_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_mctx_3444_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_zetaDeltaFVarIds_3445_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v_postponed_3446_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v_diag_3447_);
v___x_3454_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = lean_st_ref_put(v___y_3421_, v___x_3454_);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3451_);
return v___x_3456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
return v_res_3481_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3490_ = l_Lean_stringToMessageData(v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v___x_3502_; lean_object* v_env_3503_; lean_object* v_ref_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; 
v___x_3502_ = lean_st_ref_get(v_a_3500_);
v_env_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc_ref(v_env_3503_);
lean_dec(v___x_3502_);
v_ref_3504_ = lean_ctor_get(v_a_3499_, 2);
v___x_3505_ = 1;
lean_inc(v_declName_3494_);
v___x_3506_ = l_Lean_findInternalDocString_x3f(v_env_3503_, v_declName_3494_, v___x_3505_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3506_, 1);
if (lean_obj_tag(v_a_3507_) == 1)
{
lean_object* v_val_3508_; 
v_val_3508_ = lean_ctor_get(v_a_3507_, 0);
lean_inc(v_val_3508_);
lean_dec_ref_known(v_a_3507_, 1);
if (lean_obj_tag(v_val_3508_) == 0)
{
lean_object* v_val_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3530_; 
v_val_3509_ = lean_ctor_get(v_val_3508_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_val_3508_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3511_ = v_val_3508_;
v_isShared_3512_ = v_isSharedCheck_3530_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_val_3509_);
lean_dec(v_val_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3530_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_removeBuiltinDocString(v_declName_3494_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; 
lean_dec_ref_known(v___x_3513_, 1);
lean_del_object(v___x_3511_);
lean_inc(v_declName_3494_);
v___x_3514_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3515_; 
lean_dec_ref_known(v___x_3514_, 1);
v___x_3515_ = l_Lean_addVersoDocStringFromString(v_declName_3494_, v_val_3509_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
return v___x_3515_;
}
else
{
lean_dec(v_val_3509_);
lean_dec(v_declName_3494_);
return v___x_3514_;
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_val_3509_);
lean_dec(v_declName_3494_);
v_a_3516_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3518_ = v___x_3513_;
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3513_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3529_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3520_ = lean_io_error_to_string(v_a_3516_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set_tag(v___x_3511_, 3);
lean_ctor_set(v___x_3511_, 0, v___x_3520_);
v___x_3522_ = v___x_3511_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3523_ = l_Lean_MessageData_ofFormat(v___x_3522_);
lean_inc(v_ref_3504_);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v_ref_3504_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3524_);
v___x_3526_ = v___x_3518_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
else
{
lean_object* v___x_3531_; uint8_t v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec(v_val_3508_);
v___x_3531_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3532_ = 0;
v___x_3533_ = l_Lean_MessageData_ofConstName(v_declName_3494_, v___x_3532_);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3531_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3536_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
return v___x_3537_;
}
}
else
{
lean_object* v___x_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec(v_a_3507_);
v___x_3538_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3539_ = 0;
v___x_3540_ = l_Lean_MessageData_ofConstName(v_declName_3494_, v___x_3539_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3538_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
v___x_3542_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3541_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
v___x_3544_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3543_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
return v___x_3544_;
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v_declName_3494_);
v_a_3545_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3547_ = v___x_3506_;
v_isShared_3548_ = v_isSharedCheck_3556_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3506_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3556_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3549_ = lean_io_error_to_string(v_a_3545_);
v___x_3550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
v___x_3551_ = l_Lean_MessageData_ofFormat(v___x_3550_);
lean_inc(v_ref_3504_);
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_ref_3504_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3552_);
v___x_3554_ = v___x_3547_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Lean_makeDocStringVerso(v_declName_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3566_, lean_object* v_k_3567_, lean_object* v_t_3568_, lean_object* v_h_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3567_, v_t_3568_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_k_3572_, lean_object* v_t_3573_, lean_object* v_h_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3571_, v_k_3572_, v_t_3573_, v_h_3574_);
lean_dec(v_k_3572_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3576_, lean_object* v_binders_3577_, lean_object* v_docComment_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
uint8_t v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = l_Lean_isVersoDocComment(v_docComment_3578_);
v___x_3587_ = l_Lean_addDocStringOf(v___x_3586_, v_declName_3576_, v_binders_3577_, v_docComment_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3588_, lean_object* v_binders_3589_, lean_object* v_docComment_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Lean_addDocString(v_declName_3588_, v_binders_3589_, v_docComment_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3599_, lean_object* v_binders_3600_, lean_object* v_docString_x3f_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3601_) == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec(v_binders_3600_);
lean_dec(v_declName_3599_);
v___x_3609_ = lean_box(0);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3612_; 
v_val_3611_ = lean_ctor_get(v_docString_x3f_3601_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v_docString_x3f_3601_, 1);
v___x_3612_ = l_Lean_addDocString(v_declName_3599_, v_binders_3600_, v_val_3611_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3613_, lean_object* v_binders_3614_, lean_object* v_docString_x3f_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l_Lean_addDocString_x27(v_declName_3613_, v_binders_3614_, v_docString_x3f_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v_nextMacroScope_3629_; lean_object* v_ngen_3630_; lean_object* v_auxDeclNGen_3631_; lean_object* v_traceState_3632_; lean_object* v_messages_3633_; lean_object* v_infoState_3634_; lean_object* v_snapshotTasks_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3661_; 
v___x_3628_ = lean_st_ref_take(v___y_3626_);
v_nextMacroScope_3629_ = lean_ctor_get(v___x_3628_, 1);
v_ngen_3630_ = lean_ctor_get(v___x_3628_, 2);
v_auxDeclNGen_3631_ = lean_ctor_get(v___x_3628_, 3);
v_traceState_3632_ = lean_ctor_get(v___x_3628_, 4);
v_messages_3633_ = lean_ctor_get(v___x_3628_, 6);
v_infoState_3634_ = lean_ctor_get(v___x_3628_, 7);
v_snapshotTasks_3635_ = lean_ctor_get(v___x_3628_, 8);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; lean_object* v_unused_3663_; 
v_unused_3662_ = lean_ctor_get(v___x_3628_, 5);
lean_dec(v_unused_3662_);
v_unused_3663_ = lean_ctor_get(v___x_3628_, 0);
lean_dec(v_unused_3663_);
v___x_3637_ = v___x_3628_;
v_isShared_3638_ = v_isSharedCheck_3661_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_snapshotTasks_3635_);
lean_inc(v_infoState_3634_);
lean_inc(v_messages_3633_);
lean_inc(v_traceState_3632_);
lean_inc(v_auxDeclNGen_3631_);
lean_inc(v_ngen_3630_);
lean_inc(v_nextMacroScope_3629_);
lean_dec(v___x_3628_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3661_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 5, v___x_3639_);
lean_ctor_set(v___x_3637_, 0, v_env_3624_);
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_env_3624_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_nextMacroScope_3629_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_ngen_3630_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_auxDeclNGen_3631_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_traceState_3632_);
lean_ctor_set(v_reuseFailAlloc_3660_, 5, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3660_, 6, v_messages_3633_);
lean_ctor_set(v_reuseFailAlloc_3660_, 7, v_infoState_3634_);
lean_ctor_set(v_reuseFailAlloc_3660_, 8, v_snapshotTasks_3635_);
v___x_3641_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_mctx_3644_; lean_object* v_zetaDeltaFVarIds_3645_; lean_object* v_postponed_3646_; lean_object* v_diag_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3658_; 
v___x_3642_ = lean_st_ref_put(v___y_3626_, v___x_3641_);
v___x_3643_ = lean_st_ref_take(v___y_3625_);
v_mctx_3644_ = lean_ctor_get(v___x_3643_, 0);
v_zetaDeltaFVarIds_3645_ = lean_ctor_get(v___x_3643_, 2);
v_postponed_3646_ = lean_ctor_get(v___x_3643_, 3);
v_diag_3647_ = lean_ctor_get(v___x_3643_, 4);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v___x_3643_, 1);
lean_dec(v_unused_3659_);
v___x_3649_ = v___x_3643_;
v_isShared_3650_ = v_isSharedCheck_3658_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_diag_3647_);
lean_inc(v_postponed_3646_);
lean_inc(v_zetaDeltaFVarIds_3645_);
lean_inc(v_mctx_3644_);
lean_dec(v___x_3643_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3658_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3651_ = lean_box(0);
v___x_3652_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 1, v___x_3652_);
v___x_3654_ = v___x_3649_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_mctx_3644_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_zetaDeltaFVarIds_3645_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_postponed_3646_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v_diag_3647_);
v___x_3654_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_st_ref_put(v___y_3625_, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3651_);
return v___x_3656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec(v___y_3665_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3669_, lean_object* v_as_3670_, size_t v_i_3671_, size_t v_stop_3672_, lean_object* v_b_3673_){
_start:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_usize_dec_eq(v_i_3671_, v_stop_3672_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v_index_3676_; lean_object* v_sourceString_3677_; lean_object* v_imports_3678_; lean_object* v_currNamespace_3679_; lean_object* v_openDecls_3680_; lean_object* v_options_3681_; lean_object* v_check_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3698_; 
v___x_3675_ = lean_array_uget(v_as_3670_, v_i_3671_);
v_index_3676_ = lean_ctor_get(v___x_3675_, 1);
v_sourceString_3677_ = lean_ctor_get(v___x_3675_, 2);
v_imports_3678_ = lean_ctor_get(v___x_3675_, 3);
v_currNamespace_3679_ = lean_ctor_get(v___x_3675_, 4);
v_openDecls_3680_ = lean_ctor_get(v___x_3675_, 5);
v_options_3681_ = lean_ctor_get(v___x_3675_, 6);
v_check_3682_ = lean_ctor_get(v___x_3675_, 7);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; 
v_unused_3699_ = lean_ctor_get(v___x_3675_, 0);
lean_dec(v_unused_3699_);
v___x_3684_ = v___x_3675_;
v_isShared_3685_ = v_isSharedCheck_3698_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_check_3682_);
lean_inc(v_options_3681_);
lean_inc(v_openDecls_3680_);
lean_inc(v_currNamespace_3679_);
lean_inc(v_imports_3678_);
lean_inc(v_sourceString_3677_);
lean_inc(v_index_3676_);
lean_dec(v___x_3675_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3698_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v_toEnvExtension_3687_; lean_object* v_asyncMode_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3686_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3687_ = lean_ctor_get(v___x_3686_, 0);
v_asyncMode_3688_ = lean_ctor_get(v_toEnvExtension_3687_, 2);
lean_inc(v_n_3669_);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_n_3669_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3689_);
v___x_3691_ = v___x_3684_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_index_3676_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_sourceString_3677_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_imports_3678_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_currNamespace_3679_);
lean_ctor_set(v_reuseFailAlloc_3697_, 5, v_openDecls_3680_);
lean_ctor_set(v_reuseFailAlloc_3697_, 6, v_options_3681_);
lean_ctor_set(v_reuseFailAlloc_3697_, 7, v_check_3682_);
v___x_3691_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; 
v___x_3692_ = lean_box(0);
v___x_3693_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3686_, v_b_3673_, v___x_3691_, v_asyncMode_3688_, v___x_3692_);
v___x_3694_ = ((size_t)1ULL);
v___x_3695_ = lean_usize_add(v_i_3671_, v___x_3694_);
v_i_3671_ = v___x_3695_;
v_b_3673_ = v___x_3693_;
goto _start;
}
}
}
else
{
lean_dec(v_n_3669_);
return v_b_3673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3700_, lean_object* v_as_3701_, lean_object* v_i_3702_, lean_object* v_stop_3703_, lean_object* v_b_3704_){
_start:
{
size_t v_i_boxed_3705_; size_t v_stop_boxed_3706_; lean_object* v_res_3707_; 
v_i_boxed_3705_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_stop_boxed_3706_ = lean_unbox_usize(v_stop_3703_);
lean_dec(v_stop_3703_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3700_, v_as_3701_, v_i_boxed_3705_, v_stop_boxed_3706_, v_b_3704_);
lean_dec_ref(v_as_3701_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3708_, lean_object* v_deferred_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v_env_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3717_ = lean_st_ref_get(v___y_3715_);
v_env_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc_ref(v_env_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = l_Lean_getMainModuleDoc(v_env_3718_);
v___x_3720_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3719_);
lean_dec_ref(v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_dec_ref(v_docs_3708_);
v___x_3721_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3722_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3721_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3722_;
}
else
{
lean_object* v___x_3723_; lean_object* v_env_3724_; lean_object* v___x_3725_; lean_object* v_size_3726_; lean_object* v___x_3727_; lean_object* v_env_3728_; lean_object* v___x_3729_; 
v___x_3723_ = lean_st_ref_get(v___y_3715_);
v_env_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc_ref(v_env_3724_);
lean_dec(v___x_3723_);
v___x_3725_ = l_Lean_getMainVersoModuleDocs(v_env_3724_);
v_size_3726_ = lean_ctor_get(v___x_3725_, 2);
lean_inc(v_size_3726_);
lean_dec_ref(v___x_3725_);
v___x_3727_ = lean_st_ref_get(v___y_3715_);
v_env_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc_ref(v_env_3728_);
lean_dec(v___x_3727_);
v___x_3729_ = l_Lean_addVersoModuleDocSnippet(v_env_3728_, v_docs_3708_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec(v_size_3726_);
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_3732_ = l_Lean_stringToMessageData(v_a_3730_);
v___x_3733_ = l_Lean_indentD(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3731_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3734_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3735_;
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v_a_3736_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3737_ = lean_unsigned_to_nat(0u);
v___x_3738_ = lean_array_get_size(v_deferred_3709_);
v___x_3739_ = lean_nat_dec_lt(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; 
lean_dec(v_size_3726_);
v___x_3740_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3736_, v___y_3713_, v___y_3715_);
return v___x_3740_;
}
else
{
size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3741_ = ((size_t)0ULL);
v___x_3742_ = lean_usize_of_nat(v___x_3738_);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3726_, v_deferred_3709_, v___x_3741_, v___x_3742_, v_a_3736_);
v___x_3744_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3743_, v___y_3713_, v___y_3715_);
return v___x_3744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3745_, lean_object* v_deferred_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3745_, v_deferred_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_deferred_3746_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3755_, lean_object* v_doc_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_versoModDocString(v_range_3755_, v_doc_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v_fst_3766_; lean_object* v_snd_3767_; lean_object* v___x_3768_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v_fst_3766_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fst_3766_);
v_snd_3767_ = lean_ctor_get(v_a_3765_, 1);
lean_inc(v_snd_3767_);
lean_dec(v_a_3765_);
v___x_3768_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3766_, v_snd_3767_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
lean_dec(v_snd_3767_);
return v___x_3768_;
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
v_a_3769_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3764_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3764_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3777_, lean_object* v_doc_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l_Lean_addVersoModDocString(v_range_3777_, v_doc_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
lean_dec(v_a_3784_);
lean_dec_ref(v_a_3783_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_doc_3778_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3787_, v___y_3791_, v___y_3793_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3804_;
}
}
lean_object* runtime_initialize_Lean_Elab_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_DeferredCheck(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
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
res = runtime_initialize_Lean_DocString_Types(builtin);
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
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
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
res = initialize_Lean_DocString_Types(builtin);
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
