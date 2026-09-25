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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
uint8_t v_suppressElabErrors_boxed_358_; uint8_t v___x_3724__boxed_359_; uint8_t v_res_360_; lean_object* v_r_361_; 
v_suppressElabErrors_boxed_358_ = lean_unbox(v_suppressElabErrors_355_);
v___x_3724__boxed_359_ = lean_unbox(v___x_356_);
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(v_suppressElabErrors_boxed_358_, v___x_3724__boxed_359_, v_x_357_);
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
lean_object* v_a_378_; lean_object* v_snd_379_; lean_object* v_fst_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_447_; 
v_a_378_ = lean_array_uget(v_as_364_, v_i_366_);
v_snd_379_ = lean_ctor_get(v_a_378_, 1);
v_fst_380_ = lean_ctor_get(v_a_378_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_378_);
if (v_isSharedCheck_447_ == 0)
{
v___x_382_ = v_a_378_;
v_isShared_383_ = v_isSharedCheck_447_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_379_);
lean_inc(v_fst_380_);
lean_dec(v_a_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_447_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_snd_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_445_; 
v_snd_384_ = lean_ctor_get(v_snd_379_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_snd_379_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_snd_379_, 0);
lean_dec(v_unused_446_);
v___x_386_ = v_snd_379_;
v_isShared_387_ = v_isSharedCheck_445_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_snd_384_);
lean_dec(v_snd_379_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_445_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
uint8_t v_suppressElabErrors_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___y_392_; lean_object* v___y_393_; 
v_suppressElabErrors_388_ = lean_ctor_get_uint8(v___y_368_, sizeof(void*)*3 + 2);
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
lean_object* v_data_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___f_443_; uint8_t v___x_444_; 
v_data_438_ = lean_ctor_get(v___x_390_, 4);
lean_inc(v_data_438_);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_nat_dec_eq(v___x_363_, v___x_439_);
v___x_441_ = lean_box(v_suppressElabErrors_388_);
v___x_442_ = lean_box(v___x_440_);
v___f_443_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_443_, 0, v___x_441_);
lean_closure_set(v___f_443_, 1, v___x_442_);
v___x_444_ = l_Lean_MessageData_hasTag(v___f_443_, v_data_438_);
if (v___x_444_ == 0)
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
lean_object* v_toCold_394_; lean_object* v_fileName_395_; lean_object* v_pos_396_; lean_object* v_endPos_397_; uint8_t v_keepFullRange_398_; uint8_t v_severity_399_; uint8_t v_isSilent_400_; lean_object* v_caption_401_; lean_object* v_data_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_437_; 
v_toCold_394_ = lean_ctor_get(v___y_392_, 0);
v_fileName_395_ = lean_ctor_get(v___x_390_, 0);
v_pos_396_ = lean_ctor_get(v___x_390_, 1);
v_endPos_397_ = lean_ctor_get(v___x_390_, 2);
v_keepFullRange_398_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5);
v_severity_399_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5 + 1);
v_isSilent_400_ = lean_ctor_get_uint8(v___x_390_, sizeof(void*)*5 + 2);
v_caption_401_ = lean_ctor_get(v___x_390_, 3);
v_data_402_ = lean_ctor_get(v___x_390_, 4);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_437_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_437_;
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
v_isShared_405_ = v_isSharedCheck_437_;
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
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_currNamespace_406_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_openDecls_407_);
v___x_409_ = v_reuseFailAlloc_436_;
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
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_data_402_);
v___x_411_ = v_reuseFailAlloc_435_;
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
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_fileName_395_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_pos_396_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_endPos_397_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_caption_401_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v___x_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*5, v_keepFullRange_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*5 + 1, v_severity_399_);
lean_ctor_set_uint8(v_reuseFailAlloc_434_, sizeof(void*)*5 + 2, v_isSilent_400_);
v___x_413_ = v_reuseFailAlloc_434_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v_env_415_; lean_object* v_nextMacroScope_416_; lean_object* v_ngen_417_; lean_object* v_auxDeclNGen_418_; lean_object* v_traceState_419_; lean_object* v_cache_420_; lean_object* v_recordedDeps_421_; lean_object* v_messages_422_; lean_object* v_infoState_423_; lean_object* v_snapshotTasks_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_433_; 
v___x_414_ = lean_st_ref_take(v___y_393_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
v_nextMacroScope_416_ = lean_ctor_get(v___x_414_, 1);
v_ngen_417_ = lean_ctor_get(v___x_414_, 2);
v_auxDeclNGen_418_ = lean_ctor_get(v___x_414_, 3);
v_traceState_419_ = lean_ctor_get(v___x_414_, 4);
v_cache_420_ = lean_ctor_get(v___x_414_, 5);
v_recordedDeps_421_ = lean_ctor_get(v___x_414_, 6);
v_messages_422_ = lean_ctor_get(v___x_414_, 7);
v_infoState_423_ = lean_ctor_get(v___x_414_, 8);
v_snapshotTasks_424_ = lean_ctor_get(v___x_414_, 9);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_433_ == 0)
{
v___x_426_ = v___x_414_;
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snapshotTasks_424_);
lean_inc(v_infoState_423_);
lean_inc(v_messages_422_);
lean_inc(v_recordedDeps_421_);
lean_inc(v_cache_420_);
lean_inc(v_traceState_419_);
lean_inc(v_auxDeclNGen_418_);
lean_inc(v_ngen_417_);
lean_inc(v_nextMacroScope_416_);
lean_inc(v_env_415_);
lean_dec(v___x_414_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_433_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_MessageLog_add(v___x_413_, v_messages_422_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 7, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_env_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_nextMacroScope_416_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_ngen_417_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_auxDeclNGen_418_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v_traceState_419_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_cache_420_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v_recordedDeps_421_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_infoState_423_);
lean_ctor_set(v_reuseFailAlloc_432_, 9, v_snapshotTasks_424_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_st_ref_put(v___y_393_, v___x_430_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___boxed(lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v_as_450_, lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_b_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
size_t v_sz_boxed_457_; size_t v_i_boxed_458_; lean_object* v_res_459_; 
v_sz_boxed_457_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_458_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_448_, v___x_449_, v_as_450_, v_sz_boxed_457_, v_i_boxed_458_, v_b_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_as_450_);
lean_dec(v___x_449_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt(lean_object* v_openPos_460_, lean_object* v_startPos_461_, lean_object* v_endPos_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_toCold_466_; lean_object* v_fileMap_467_; lean_object* v_fileName_468_; lean_object* v_currNamespace_469_; lean_object* v_openDecls_470_; lean_object* v_source_471_; lean_object* v___y_473_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_toCold_466_ = lean_ctor_get(v_a_463_, 0);
v_fileMap_467_ = lean_ctor_get(v_toCold_466_, 1);
v_fileName_468_ = lean_ctor_get(v_toCold_466_, 0);
v_currNamespace_469_ = lean_ctor_get(v_toCold_466_, 4);
v_openDecls_470_ = lean_ctor_get(v_toCold_466_, 5);
v_source_471_ = lean_ctor_get(v_fileMap_467_, 0);
v___x_514_ = lean_string_utf8_byte_size(v_source_471_);
v___x_515_ = lean_nat_dec_le(v_endPos_462_, v___x_514_);
if (v___x_515_ == 0)
{
lean_dec(v_endPos_462_);
v___y_473_ = v___x_514_;
goto v___jp_472_;
}
else
{
v___y_473_ = v_endPos_462_;
goto v___jp_472_;
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v_env_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_474_ = lean_st_ref_get(v_a_464_);
v_env_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref_n(v_env_475_, 2);
lean_dec(v___x_474_);
lean_inc(v___y_473_);
lean_inc_ref_n(v_fileMap_467_, 2);
lean_inc_ref(v_fileName_468_);
lean_inc_ref(v_source_471_);
v___x_476_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_476_, 0, v_source_471_);
lean_ctor_set(v___x_476_, 1, v_fileName_468_);
lean_ctor_set(v___x_476_, 2, v_fileMap_467_);
lean_ctor_set(v___x_476_, 3, v___y_473_);
v___x_477_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_463_);
lean_inc(v_openDecls_470_);
lean_inc(v_currNamespace_469_);
v___x_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_478_, 0, v_env_475_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
lean_ctor_set(v___x_478_, 2, v_currNamespace_469_);
lean_ctor_set(v___x_478_, 3, v_openDecls_470_);
lean_inc(v_startPos_461_);
v___x_479_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_467_, v_openPos_460_, v_startPos_461_, v___y_473_);
v___x_480_ = l_Lean_Parser_mkParserState(v_source_471_);
v___x_481_ = l_Lean_Parser_ParserState_setPos(v___x_480_, v_startPos_461_);
v___x_482_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_482_, 0, v___x_479_);
v___x_483_ = l_Lean_Parser_getTokenTable(v_env_475_);
lean_inc_ref(v___x_476_);
v___x_484_ = l_Lean_Parser_ParserFn_run(v___x_482_, v___x_476_, v___x_478_, v___x_483_, v___x_481_);
lean_inc_ref(v___x_484_);
v___x_485_ = l_Lean_Parser_ParserState_allErrors(v___x_484_);
v___x_486_ = lean_array_get_size(v___x_485_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; size_t v_sz_490_; size_t v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v___x_484_);
v___x_489_ = lean_box(0);
v_sz_490_ = lean_array_size(v___x_485_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_476_, v___x_486_, v___x_485_, v_sz_490_, v___x_491_, v___x_489_, v_a_463_, v_a_464_);
lean_dec_ref(v___x_485_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_500_; 
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_492_, 0);
lean_dec(v_unused_501_);
v___x_494_ = v___x_492_;
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
else
{
lean_dec(v___x_492_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_box(0);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_492_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_492_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_stxStack_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v___x_485_);
lean_dec_ref_known(v___x_476_, 4);
v_stxStack_510_ = lean_ctor_get(v___x_484_, 0);
lean_inc_ref(v_stxStack_510_);
lean_dec_ref(v___x_484_);
v___x_511_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_510_);
lean_dec_ref(v_stxStack_510_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocStringAt___boxed(lean_object* v_openPos_516_, lean_object* v_startPos_517_, lean_object* v_endPos_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_parseVersoDocStringAt(v_openPos_516_, v_startPos_517_, v_endPos_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_openPos_516_);
return v_res_522_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_523_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
lean_ctor_set(v___x_528_, 3, v___x_527_);
lean_ctor_set(v___x_528_, 4, v___x_526_);
lean_ctor_set(v___x_528_, 5, v___x_526_);
lean_ctor_set(v___x_528_, 6, v___x_526_);
lean_ctor_set(v___x_528_, 7, v___x_526_);
lean_ctor_set(v___x_528_, 8, v___x_526_);
lean_ctor_set(v___x_528_, 9, v___x_526_);
lean_ctor_set(v___x_528_, 10, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_unsigned_to_nat(32u);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = ((size_t)5ULL);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_unsigned_to_nat(32u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__3);
v___x_537_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_533_);
lean_ctor_set(v___x_537_, 3, v___x_533_);
lean_ctor_set_usize(v___x_537_, 4, v___x_532_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = lean_box(1);
v___x_539_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__4);
v___x_540_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__1);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_539_);
lean_ctor_set(v___x_541_, 2, v___x_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; lean_object* v_toCold_547_; lean_object* v_env_548_; lean_object* v_options_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_546_ = lean_st_ref_get(v___y_544_);
v_toCold_547_ = lean_ctor_get(v___y_543_, 0);
v_env_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_546_);
v_options_549_ = lean_ctor_get(v_toCold_547_, 2);
v___x_550_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2);
v___x_551_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_549_);
v___x_552_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_552_, 0, v_env_548_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
lean_ctor_set(v___x_552_, 3, v_options_549_);
v___x_553_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_msgData_542_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object* v_msgData_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_ref_564_; lean_object* v___x_565_; lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_574_; 
v_ref_564_ = lean_ctor_get(v___y_561_, 2);
v___x_565_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msg_560_, v___y_561_, v___y_562_);
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_574_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_574_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
lean_inc(v_ref_564_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_ref_564_);
lean_ctor_set(v___x_570_, 1, v_a_566_);
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 1);
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_docComment_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_____x_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_580_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_594_, v_a_581_, v_a_582_);
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; 
v_a_604_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_593_, 1);
v_____x_585_ = v_a_604_;
v___y_586_ = v_a_581_;
v___y_587_ = v_a_582_;
goto v___jp_584_;
}
v___jp_584_:
{
lean_object* v_snd_588_; lean_object* v_fst_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_592_; 
v_snd_588_ = lean_ctor_get(v_____x_585_, 1);
lean_inc(v_snd_588_);
v_fst_589_ = lean_ctor_get(v_____x_585_, 0);
lean_inc(v_fst_589_);
lean_dec_ref(v_____x_585_);
v_fst_590_ = lean_ctor_get(v_snd_588_, 0);
lean_inc(v_fst_590_);
v_snd_591_ = lean_ctor_get(v_snd_588_, 1);
lean_inc(v_snd_591_);
lean_dec(v_snd_588_);
v___x_592_ = l_Lean_parseVersoDocStringAt(v_fst_589_, v_fst_590_, v_snd_591_, v___y_586_, v___y_587_);
lean_dec(v_fst_589_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object* v_docComment_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_parseVersoDocString(v_docComment_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_docComment_605_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object* v_00_u03b1_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_611_, v___y_612_, v___y_613_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object* v_00_u03b1_616_, lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(v_00_u03b1_616_, v_msg_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_view_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_____x_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___x_652_; 
v___x_652_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_622_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_653_, v_a_623_, v_a_624_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_663_; 
v_a_663_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_652_, 1);
v_____x_627_ = v_a_663_;
v___y_628_ = v_a_623_;
v___y_629_ = v_a_624_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v_snd_630_; lean_object* v_fst_631_; lean_object* v_fst_632_; lean_object* v_snd_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_snd_630_ = lean_ctor_get(v_____x_627_, 1);
lean_inc(v_snd_630_);
v_fst_631_ = lean_ctor_get(v_____x_627_, 0);
lean_inc(v_fst_631_);
lean_dec_ref(v_____x_627_);
v_fst_632_ = lean_ctor_get(v_snd_630_, 0);
lean_inc(v_fst_632_);
v_snd_633_ = lean_ctor_get(v_snd_630_, 1);
lean_inc(v_snd_633_);
lean_dec(v_snd_630_);
v___x_634_ = lean_box(0);
v___x_635_ = l_Lean_parseVersoDocStringAt(v_fst_631_, v_fst_632_, v_snd_633_, v___y_628_, v___y_629_);
lean_dec(v_fst_631_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_635_, 0);
lean_dec(v_unused_643_);
v___x_637_ = v___x_635_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_dec(v___x_635_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_634_);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_634_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_635_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_635_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_view_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_reportVersoParseFailure(v_view_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec_ref(v_view_664_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_669_, lean_object* v_declName_670_, lean_object* v_binders_671_, lean_object* v___x_672_, uint8_t v___x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_669_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Doc_DocM_exec___redArg(v_declName_670_, v_binders_671_, v___x_672_, v___x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_681_;
}
else
{
lean_object* v_toCold_682_; lean_object* v_val_683_; lean_object* v_currRecDepth_684_; lean_object* v_ref_685_; uint16_t v_optionFlags_686_; uint8_t v_suppressElabErrors_687_; uint8_t v_isRecordingDeps_688_; lean_object* v_fileName_689_; lean_object* v_options_690_; lean_object* v_maxRecDepth_691_; lean_object* v_currNamespace_692_; lean_object* v_openDecls_693_; lean_object* v_initHeartbeats_694_; lean_object* v_maxHeartbeats_695_; lean_object* v_quotContext_696_; lean_object* v_currMacroScope_697_; lean_object* v_cancelTk_x3f_698_; lean_object* v_inheritedTraceOptions_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_toCold_682_ = lean_ctor_get(v___y_678_, 0);
v_val_683_ = lean_ctor_get(v_fileMap_x3f_669_, 0);
v_currRecDepth_684_ = lean_ctor_get(v___y_678_, 1);
v_ref_685_ = lean_ctor_get(v___y_678_, 2);
v_optionFlags_686_ = lean_ctor_get_uint16(v___y_678_, sizeof(void*)*3);
v_suppressElabErrors_687_ = lean_ctor_get_uint8(v___y_678_, sizeof(void*)*3 + 2);
v_isRecordingDeps_688_ = lean_ctor_get_uint8(v___y_678_, sizeof(void*)*3 + 3);
v_fileName_689_ = lean_ctor_get(v_toCold_682_, 0);
v_options_690_ = lean_ctor_get(v_toCold_682_, 2);
v_maxRecDepth_691_ = lean_ctor_get(v_toCold_682_, 3);
v_currNamespace_692_ = lean_ctor_get(v_toCold_682_, 4);
v_openDecls_693_ = lean_ctor_get(v_toCold_682_, 5);
v_initHeartbeats_694_ = lean_ctor_get(v_toCold_682_, 6);
v_maxHeartbeats_695_ = lean_ctor_get(v_toCold_682_, 7);
v_quotContext_696_ = lean_ctor_get(v_toCold_682_, 8);
v_currMacroScope_697_ = lean_ctor_get(v_toCold_682_, 9);
v_cancelTk_x3f_698_ = lean_ctor_get(v_toCold_682_, 10);
v_inheritedTraceOptions_699_ = lean_ctor_get(v_toCold_682_, 11);
lean_inc_ref(v_inheritedTraceOptions_699_);
lean_inc(v_cancelTk_x3f_698_);
lean_inc(v_currMacroScope_697_);
lean_inc(v_quotContext_696_);
lean_inc(v_maxHeartbeats_695_);
lean_inc(v_initHeartbeats_694_);
lean_inc(v_openDecls_693_);
lean_inc(v_currNamespace_692_);
lean_inc(v_maxRecDepth_691_);
lean_inc_ref(v_options_690_);
lean_inc(v_val_683_);
lean_inc_ref(v_fileName_689_);
v___x_700_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_700_, 0, v_fileName_689_);
lean_ctor_set(v___x_700_, 1, v_val_683_);
lean_ctor_set(v___x_700_, 2, v_options_690_);
lean_ctor_set(v___x_700_, 3, v_maxRecDepth_691_);
lean_ctor_set(v___x_700_, 4, v_currNamespace_692_);
lean_ctor_set(v___x_700_, 5, v_openDecls_693_);
lean_ctor_set(v___x_700_, 6, v_initHeartbeats_694_);
lean_ctor_set(v___x_700_, 7, v_maxHeartbeats_695_);
lean_ctor_set(v___x_700_, 8, v_quotContext_696_);
lean_ctor_set(v___x_700_, 9, v_currMacroScope_697_);
lean_ctor_set(v___x_700_, 10, v_cancelTk_x3f_698_);
lean_ctor_set(v___x_700_, 11, v_inheritedTraceOptions_699_);
lean_inc(v_ref_685_);
lean_inc(v_currRecDepth_684_);
v___x_701_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_currRecDepth_684_);
lean_ctor_set(v___x_701_, 2, v_ref_685_);
lean_ctor_set_uint16(v___x_701_, sizeof(void*)*3, v_optionFlags_686_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*3 + 2, v_suppressElabErrors_687_);
lean_ctor_set_uint8(v___x_701_, sizeof(void*)*3 + 3, v_isRecordingDeps_688_);
v___x_702_ = l_Lean_Doc_DocM_exec___redArg(v_declName_670_, v_binders_671_, v___x_672_, v___x_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___x_701_, v___y_679_);
lean_dec_ref_known(v___x_701_, 3);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_703_, lean_object* v_declName_704_, lean_object* v_binders_705_, lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_9830__boxed_715_; lean_object* v_res_716_; 
v___x_9830__boxed_715_ = lean_unbox(v___x_707_);
v_res_716_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_703_, v_declName_704_, v_binders_705_, v___x_706_, v___x_9830__boxed_715_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v_fileMap_x3f_703_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_717_, size_t v_i_718_, lean_object* v_bs_719_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_718_, v_sz_717_);
if (v___x_720_ == 0)
{
return v_bs_719_;
}
else
{
lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v_v_721_ = lean_array_uget(v_bs_719_, v_i_718_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_719_, v_i_718_, v___x_722_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_718_, v___x_724_);
v___x_726_ = lean_array_uset(v_bs_x27_723_, v_i_718_, v_v_721_);
v_i_718_ = v___x_725_;
v_bs_719_ = v___x_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_728_, lean_object* v_i_729_, lean_object* v_bs_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_732_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_731_, v_i_boxed_732_, v_bs_730_);
return v_res_733_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_734_, lean_object* v_opt_735_){
_start:
{
lean_object* v_name_736_; lean_object* v_defValue_737_; lean_object* v_map_738_; lean_object* v___x_739_; 
v_name_736_ = lean_ctor_get(v_opt_735_, 0);
v_defValue_737_ = lean_ctor_get(v_opt_735_, 1);
v_map_738_ = lean_ctor_get(v_opts_734_, 0);
v___x_739_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_738_, v_name_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v_defValue_737_);
return v___x_740_;
}
else
{
lean_object* v_val_741_; 
v_val_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_741_);
lean_dec_ref_known(v___x_739_, 1);
if (lean_obj_tag(v_val_741_) == 1)
{
uint8_t v_v_742_; 
v_v_742_ = lean_ctor_get_uint8(v_val_741_, 0);
lean_dec_ref_known(v_val_741_, 0);
return v_v_742_;
}
else
{
uint8_t v___x_743_; 
lean_dec(v_val_741_);
v___x_743_ = lean_unbox(v_defValue_737_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_744_, lean_object* v_opt_745_){
_start:
{
uint8_t v_res_746_; lean_object* v_r_747_; 
v_res_746_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_744_, v_opt_745_);
lean_dec_ref(v_opt_745_);
lean_dec_ref(v_opts_744_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; lean_object* v_env_755_; lean_object* v___x_756_; lean_object* v_toCold_757_; lean_object* v_mctx_758_; lean_object* v_lctx_759_; lean_object* v_options_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_754_ = lean_st_ref_get(v___y_752_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_env_755_);
lean_dec(v___x_754_);
v___x_756_ = lean_st_ref_get(v___y_750_);
v_toCold_757_ = lean_ctor_get(v___y_751_, 0);
v_mctx_758_ = lean_ctor_get(v___x_756_, 0);
lean_inc_ref(v_mctx_758_);
lean_dec(v___x_756_);
v_lctx_759_ = lean_ctor_get(v___y_749_, 2);
v_options_760_ = lean_ctor_get(v_toCold_757_, 2);
lean_inc_ref(v_options_760_);
lean_inc_ref(v_lctx_759_);
v___x_761_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_761_, 0, v_env_755_);
lean_ctor_set(v___x_761_, 1, v_mctx_758_);
lean_ctor_set(v___x_761_, 2, v_lctx_759_);
lean_ctor_set(v___x_761_, 3, v_options_760_);
v___x_762_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v_msgData_748_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_771_, uint8_t v___y_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_773_) == 1)
{
lean_object* v_pre_774_; 
v_pre_774_ = lean_ctor_get(v_x_773_, 0);
switch(lean_obj_tag(v_pre_774_))
{
case 1:
{
lean_object* v_pre_775_; 
v_pre_775_ = lean_ctor_get(v_pre_774_, 0);
switch(lean_obj_tag(v_pre_775_))
{
case 0:
{
lean_object* v_str_776_; lean_object* v_str_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_str_776_ = lean_ctor_get(v_x_773_, 1);
v_str_777_ = lean_ctor_get(v_pre_774_, 1);
v___x_778_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_779_ = lean_string_dec_eq(v_str_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_781_ = lean_string_dec_eq(v_str_777_, v___x_780_);
if (v___x_781_ == 0)
{
return v___x_781_;
}
else
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_783_ = lean_string_dec_eq(v_str_776_, v___x_782_);
if (v___x_783_ == 0)
{
return v___x_783_;
}
else
{
return v_suppressElabErrors_771_;
}
}
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_785_ = lean_string_dec_eq(v_str_776_, v___x_784_);
if (v___x_785_ == 0)
{
return v___x_785_;
}
else
{
return v_suppressElabErrors_771_;
}
}
}
case 1:
{
lean_object* v_pre_786_; 
v_pre_786_ = lean_ctor_get(v_pre_775_, 0);
if (lean_obj_tag(v_pre_786_) == 0)
{
lean_object* v_str_787_; lean_object* v_str_788_; lean_object* v_str_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_str_787_ = lean_ctor_get(v_x_773_, 1);
v_str_788_ = lean_ctor_get(v_pre_774_, 1);
v_str_789_ = lean_ctor_get(v_pre_775_, 1);
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_791_ = lean_string_dec_eq(v_str_789_, v___x_790_);
if (v___x_791_ == 0)
{
return v___x_791_;
}
else
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_793_ = lean_string_dec_eq(v_str_788_, v___x_792_);
if (v___x_793_ == 0)
{
return v___x_793_;
}
else
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_795_ = lean_string_dec_eq(v_str_787_, v___x_794_);
if (v___x_795_ == 0)
{
return v___x_795_;
}
else
{
return v_suppressElabErrors_771_;
}
}
}
}
else
{
return v___y_772_;
}
}
default: 
{
return v___y_772_;
}
}
}
case 0:
{
lean_object* v_str_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_str_796_ = lean_ctor_get(v_x_773_, 1);
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_798_ = lean_string_dec_eq(v_str_796_, v___x_797_);
if (v___x_798_ == 0)
{
return v___x_798_;
}
else
{
return v_suppressElabErrors_771_;
}
}
default: 
{
return v___y_772_;
}
}
}
else
{
return v___y_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_799_, lean_object* v___y_800_, lean_object* v_x_801_){
_start:
{
uint8_t v_suppressElabErrors_boxed_802_; uint8_t v___y_9921__boxed_803_; uint8_t v_res_804_; lean_object* v_r_805_; 
v_suppressElabErrors_boxed_802_ = lean_unbox(v_suppressElabErrors_799_);
v___y_9921__boxed_803_ = lean_unbox(v___y_800_);
v_res_804_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_802_, v___y_9921__boxed_803_, v_x_801_);
lean_dec(v_x_801_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_806_, lean_object* v_msgData_807_, uint8_t v_severity_808_, uint8_t v_isSilent_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___y_816_; uint8_t v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; uint8_t v___y_822_; lean_object* v_toCold_823_; lean_object* v___y_824_; lean_object* v___y_853_; lean_object* v___y_854_; uint8_t v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; uint8_t v___y_859_; lean_object* v___y_860_; lean_object* v___y_880_; lean_object* v___y_881_; uint8_t v___y_882_; uint8_t v___y_883_; uint8_t v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_890_; uint8_t v___y_891_; uint8_t v___y_892_; uint8_t v___x_903_; uint8_t v___y_905_; uint8_t v___y_906_; uint8_t v___y_907_; uint8_t v___y_909_; uint8_t v___x_917_; 
v___x_903_ = 2;
v___x_917_ = l_Lean_instBEqMessageSeverity_beq(v_severity_808_, v___x_903_);
if (v___x_917_ == 0)
{
v___y_909_ = v___x_917_;
goto v___jp_908_;
}
else
{
uint8_t v___x_918_; 
lean_inc_ref(v_msgData_807_);
v___x_918_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_807_);
v___y_909_ = v___x_918_;
goto v___jp_908_;
}
v___jp_815_:
{
lean_object* v_currNamespace_825_; lean_object* v_openDecls_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_env_831_; lean_object* v_nextMacroScope_832_; lean_object* v_ngen_833_; lean_object* v_auxDeclNGen_834_; lean_object* v_traceState_835_; lean_object* v_cache_836_; lean_object* v_recordedDeps_837_; lean_object* v_messages_838_; lean_object* v_infoState_839_; lean_object* v_snapshotTasks_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v_currNamespace_825_ = lean_ctor_get(v_toCold_823_, 4);
v_openDecls_826_ = lean_ctor_get(v_toCold_823_, 5);
lean_inc(v_openDecls_826_);
lean_inc(v_currNamespace_825_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_currNamespace_825_);
lean_ctor_set(v___x_827_, 1, v_openDecls_826_);
v___x_828_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___y_819_);
lean_inc_ref(v___y_816_);
lean_inc_ref(v___y_821_);
v___x_829_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_829_, 0, v___y_821_);
lean_ctor_set(v___x_829_, 1, v___y_818_);
lean_ctor_set(v___x_829_, 2, v___y_820_);
lean_ctor_set(v___x_829_, 3, v___y_816_);
lean_ctor_set(v___x_829_, 4, v___x_828_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*5, v___y_817_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*5 + 1, v___y_822_);
lean_ctor_set_uint8(v___x_829_, sizeof(void*)*5 + 2, v_isSilent_809_);
v___x_830_ = lean_st_ref_take(v___y_824_);
v_env_831_ = lean_ctor_get(v___x_830_, 0);
v_nextMacroScope_832_ = lean_ctor_get(v___x_830_, 1);
v_ngen_833_ = lean_ctor_get(v___x_830_, 2);
v_auxDeclNGen_834_ = lean_ctor_get(v___x_830_, 3);
v_traceState_835_ = lean_ctor_get(v___x_830_, 4);
v_cache_836_ = lean_ctor_get(v___x_830_, 5);
v_recordedDeps_837_ = lean_ctor_get(v___x_830_, 6);
v_messages_838_ = lean_ctor_get(v___x_830_, 7);
v_infoState_839_ = lean_ctor_get(v___x_830_, 8);
v_snapshotTasks_840_ = lean_ctor_get(v___x_830_, 9);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_851_ == 0)
{
v___x_842_ = v___x_830_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snapshotTasks_840_);
lean_inc(v_infoState_839_);
lean_inc(v_messages_838_);
lean_inc(v_recordedDeps_837_);
lean_inc(v_cache_836_);
lean_inc(v_traceState_835_);
lean_inc(v_auxDeclNGen_834_);
lean_inc(v_ngen_833_);
lean_inc(v_nextMacroScope_832_);
lean_inc(v_env_831_);
lean_dec(v___x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_844_ = lean_box(0);
v___x_845_ = l_Lean_MessageLog_add(v___x_829_, v_messages_838_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 7, v___x_845_);
v___x_847_ = v___x_842_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_env_831_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_nextMacroScope_832_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_ngen_833_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_auxDeclNGen_834_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v_traceState_835_);
lean_ctor_set(v_reuseFailAlloc_850_, 5, v_cache_836_);
lean_ctor_set(v_reuseFailAlloc_850_, 6, v_recordedDeps_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 7, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_850_, 8, v_infoState_839_);
lean_ctor_set(v_reuseFailAlloc_850_, 9, v_snapshotTasks_840_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_st_ref_put(v___y_824_, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_844_);
return v___x_849_;
}
}
}
v___jp_852_:
{
lean_object* v_fileName_861_; lean_object* v_fileMap_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_878_; 
v_fileName_861_ = lean_ctor_get(v___y_857_, 0);
v_fileMap_862_ = lean_ctor_get(v___y_857_, 1);
v___x_863_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_807_);
v___x_864_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_863_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_878_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_878_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_inc_ref_n(v_fileMap_862_, 2);
v___x_869_ = l_Lean_FileMap_toPosition(v_fileMap_862_, v___y_856_);
lean_dec(v___y_856_);
v___x_870_ = l_Lean_FileMap_toPosition(v_fileMap_862_, v___y_860_);
lean_dec(v___y_860_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
v___x_872_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_858_ == 0)
{
lean_del_object(v___x_867_);
lean_dec_ref(v___y_853_);
v___y_816_ = v___x_872_;
v___y_817_ = v___y_855_;
v___y_818_ = v___x_869_;
v___y_819_ = v_a_865_;
v___y_820_ = v___x_871_;
v___y_821_ = v_fileName_861_;
v___y_822_ = v___y_859_;
v_toCold_823_ = v___y_854_;
v___y_824_ = v___y_813_;
goto v___jp_815_;
}
else
{
uint8_t v___x_873_; 
lean_inc(v_a_865_);
v___x_873_ = l_Lean_MessageData_hasTag(v___y_853_, v_a_865_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec_ref_known(v___x_871_, 1);
lean_dec_ref(v___x_869_);
lean_dec(v_a_865_);
v___x_874_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_874_);
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_del_object(v___x_867_);
v___y_816_ = v___x_872_;
v___y_817_ = v___y_855_;
v___y_818_ = v___x_869_;
v___y_819_ = v_a_865_;
v___y_820_ = v___x_871_;
v___y_821_ = v_fileName_861_;
v___y_822_ = v___y_859_;
v_toCold_823_ = v___y_854_;
v___y_824_ = v___y_813_;
goto v___jp_815_;
}
}
}
}
v___jp_879_:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Syntax_getTailPos_x3f(v___y_885_, v___y_883_);
lean_dec(v___y_885_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_inc(v___y_886_);
v___y_853_ = v___y_880_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_883_;
v___y_856_ = v___y_886_;
v___y_857_ = v___y_881_;
v___y_858_ = v___y_882_;
v___y_859_ = v___y_884_;
v___y_860_ = v___y_886_;
goto v___jp_852_;
}
else
{
lean_object* v_val_888_; 
v_val_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v___x_887_, 1);
v___y_853_ = v___y_880_;
v___y_854_ = v___y_881_;
v___y_855_ = v___y_883_;
v___y_856_ = v___y_886_;
v___y_857_ = v___y_881_;
v___y_858_ = v___y_882_;
v___y_859_ = v___y_884_;
v___y_860_ = v_val_888_;
goto v___jp_852_;
}
}
v___jp_889_:
{
lean_object* v_toCold_893_; lean_object* v_ref_894_; uint8_t v_suppressElabErrors_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___f_898_; lean_object* v_ref_899_; lean_object* v___x_900_; 
v_toCold_893_ = lean_ctor_get(v___y_812_, 0);
v_ref_894_ = lean_ctor_get(v___y_812_, 2);
v_suppressElabErrors_895_ = lean_ctor_get_uint8(v___y_812_, sizeof(void*)*3 + 2);
v___x_896_ = lean_box(v_suppressElabErrors_895_);
v___x_897_ = lean_box(v___y_890_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_898_, 0, v___x_896_);
lean_closure_set(v___f_898_, 1, v___x_897_);
v_ref_899_ = l_Lean_replaceRef(v_ref_806_, v_ref_894_);
v___x_900_ = l_Lean_Syntax_getPos_x3f(v_ref_899_, v___y_891_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; 
v___x_901_ = lean_unsigned_to_nat(0u);
v___y_880_ = v___f_898_;
v___y_881_ = v_toCold_893_;
v___y_882_ = v_suppressElabErrors_895_;
v___y_883_ = v___y_891_;
v___y_884_ = v___y_892_;
v___y_885_ = v_ref_899_;
v___y_886_ = v___x_901_;
goto v___jp_879_;
}
else
{
lean_object* v_val_902_; 
v_val_902_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v___x_900_, 1);
v___y_880_ = v___f_898_;
v___y_881_ = v_toCold_893_;
v___y_882_ = v_suppressElabErrors_895_;
v___y_883_ = v___y_891_;
v___y_884_ = v___y_892_;
v___y_885_ = v_ref_899_;
v___y_886_ = v_val_902_;
goto v___jp_879_;
}
}
v___jp_904_:
{
if (v___y_907_ == 0)
{
v___y_890_ = v___y_905_;
v___y_891_ = v___y_906_;
v___y_892_ = v_severity_808_;
goto v___jp_889_;
}
else
{
v___y_890_ = v___y_905_;
v___y_891_ = v___y_906_;
v___y_892_ = v___x_903_;
goto v___jp_889_;
}
}
v___jp_908_:
{
if (v___y_909_ == 0)
{
uint8_t v___x_910_; uint8_t v___x_911_; 
v___x_910_ = 1;
v___x_911_ = l_Lean_instBEqMessageSeverity_beq(v_severity_808_, v___x_910_);
if (v___x_911_ == 0)
{
v___y_905_ = v___y_909_;
v___y_906_ = v___y_909_;
v___y_907_ = v___x_911_;
goto v___jp_904_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_912_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_812_);
v___x_913_ = l_Lean_warningAsError;
v___x_914_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_912_, v___x_913_);
lean_dec_ref(v___x_912_);
v___y_905_ = v___y_909_;
v___y_906_ = v___y_909_;
v___y_907_ = v___x_914_;
goto v___jp_904_;
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v_msgData_807_);
v___x_915_ = lean_box(0);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_919_, lean_object* v_msgData_920_, lean_object* v_severity_921_, lean_object* v_isSilent_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v_severity_boxed_928_; uint8_t v_isSilent_boxed_929_; lean_object* v_res_930_; 
v_severity_boxed_928_ = lean_unbox(v_severity_921_);
v_isSilent_boxed_929_ = lean_unbox(v_isSilent_922_);
v_res_930_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_919_, v_msgData_920_, v_severity_boxed_928_, v_isSilent_boxed_929_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v_ref_919_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_934_);
return v___x_943_;
}
else
{
lean_object* v_ref_944_; lean_object* v_a_945_; uint8_t v_severity_946_; uint8_t v_isSilent_947_; lean_object* v_data_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_ref_944_ = lean_ctor_get(v___y_939_, 2);
v_a_945_ = lean_array_uget_borrowed(v_as_931_, v_i_933_);
v_severity_946_ = lean_ctor_get_uint8(v_a_945_, sizeof(void*)*5 + 1);
v_isSilent_947_ = lean_ctor_get_uint8(v_a_945_, sizeof(void*)*5 + 2);
v_data_948_ = lean_ctor_get(v_a_945_, 4);
v___x_949_ = lean_box(0);
lean_inc(v_data_948_);
v___x_950_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_944_, v_data_948_, v_severity_946_, v_isSilent_947_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_950_) == 0)
{
size_t v___x_951_; size_t v___x_952_; 
lean_dec_ref_known(v___x_950_, 1);
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_933_, v___x_951_);
v_i_933_ = v___x_952_;
v_b_934_ = v___x_949_;
goto _start;
}
else
{
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_954_, lean_object* v_sz_955_, lean_object* v_i_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
size_t v_sz_boxed_965_; size_t v_i_boxed_966_; lean_object* v_res_967_; 
v_sz_boxed_965_ = lean_unbox_usize(v_sz_955_);
lean_dec(v_sz_955_);
v_i_boxed_966_ = lean_unbox_usize(v_i_956_);
lean_dec(v_i_956_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_954_, v_sz_boxed_965_, v_i_boxed_966_, v_b_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec_ref(v_as_954_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_infoState_972_; lean_object* v_env_973_; lean_object* v_nextMacroScope_974_; lean_object* v_ngen_975_; lean_object* v_auxDeclNGen_976_; lean_object* v_traceState_977_; lean_object* v_cache_978_; lean_object* v_recordedDeps_979_; lean_object* v_messages_980_; lean_object* v_snapshotTasks_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1001_; 
v___x_971_ = lean_st_ref_take(v___y_969_);
v_infoState_972_ = lean_ctor_get(v___x_971_, 8);
v_env_973_ = lean_ctor_get(v___x_971_, 0);
v_nextMacroScope_974_ = lean_ctor_get(v___x_971_, 1);
v_ngen_975_ = lean_ctor_get(v___x_971_, 2);
v_auxDeclNGen_976_ = lean_ctor_get(v___x_971_, 3);
v_traceState_977_ = lean_ctor_get(v___x_971_, 4);
v_cache_978_ = lean_ctor_get(v___x_971_, 5);
v_recordedDeps_979_ = lean_ctor_get(v___x_971_, 6);
v_messages_980_ = lean_ctor_get(v___x_971_, 7);
v_snapshotTasks_981_ = lean_ctor_get(v___x_971_, 9);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_983_ = v___x_971_;
v_isShared_984_ = v_isSharedCheck_1001_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snapshotTasks_981_);
lean_inc(v_infoState_972_);
lean_inc(v_messages_980_);
lean_inc(v_recordedDeps_979_);
lean_inc(v_cache_978_);
lean_inc(v_traceState_977_);
lean_inc(v_auxDeclNGen_976_);
lean_inc(v_ngen_975_);
lean_inc(v_nextMacroScope_974_);
lean_inc(v_env_973_);
lean_dec(v___x_971_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1001_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_assignment_985_; lean_object* v_lazyAssignment_986_; lean_object* v_trees_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1000_; 
v_assignment_985_ = lean_ctor_get(v_infoState_972_, 0);
v_lazyAssignment_986_ = lean_ctor_get(v_infoState_972_, 1);
v_trees_987_ = lean_ctor_get(v_infoState_972_, 2);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_infoState_972_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_989_ = v_infoState_972_;
v_isShared_990_ = v_isSharedCheck_1000_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_trees_987_);
lean_inc(v_lazyAssignment_986_);
lean_inc(v_assignment_985_);
lean_dec(v_infoState_972_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1000_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_990_ == 0)
{
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_assignment_985_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_lazyAssignment_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_trees_987_);
v___x_993_ = v_reuseFailAlloc_999_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*3, v_flag_968_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 8, v___x_993_);
v___x_995_ = v___x_983_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_env_973_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_nextMacroScope_974_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_ngen_975_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_auxDeclNGen_976_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_traceState_977_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_cache_978_);
lean_ctor_set(v_reuseFailAlloc_998_, 6, v_recordedDeps_979_);
lean_ctor_set(v_reuseFailAlloc_998_, 7, v_messages_980_);
lean_ctor_set(v_reuseFailAlloc_998_, 8, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_998_, 9, v_snapshotTasks_981_);
v___x_995_ = v_reuseFailAlloc_998_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_st_ref_put(v___y_969_, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_991_);
return v___x_997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
uint8_t v_flag_boxed_1005_; lean_object* v_res_1006_; 
v_flag_boxed_1005_ = lean_unbox(v_flag_1002_);
v_res_1006_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1005_, v___y_1003_);
lean_dec(v___y_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v_infoState_1017_; uint8_t v_enabled_1018_; lean_object* v_a_1020_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1016_ = lean_st_ref_get(v___y_1014_);
v_infoState_1017_ = lean_ctor_get(v___x_1016_, 8);
lean_inc_ref(v_infoState_1017_);
lean_dec(v___x_1016_);
v_enabled_1018_ = lean_ctor_get_uint8(v_infoState_1017_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1017_);
v___x_1030_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1007_, v___y_1014_);
lean_dec_ref(v___x_1030_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
v___x_1031_ = lean_apply_7(v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, lean_box(0));
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v___x_1033_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1018_, v___y_1014_);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v___x_1033_, 0);
lean_dec(v_unused_1041_);
v___x_1035_ = v___x_1033_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v___x_1033_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_a_1032_);
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1032_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
else
{
lean_object* v_a_1042_; 
v_a_1042_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1031_, 1);
v_a_1020_ = v_a_1042_;
goto v___jp_1019_;
}
v___jp_1019_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v___x_1021_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1018_, v___y_1014_);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v___x_1021_, 0);
lean_dec(v_unused_1029_);
v___x_1023_ = v___x_1021_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_dec(v___x_1021_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set_tag(v___x_1023_, 1);
lean_ctor_set(v___x_1023_, 0, v_a_1020_);
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1020_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v_flag_boxed_1052_; lean_object* v_res_1053_; 
v_flag_boxed_1052_ = lean_unbox(v_flag_1043_);
v_res_1053_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1052_, v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1054_, lean_object* v_binders_1055_, lean_object* v_blocks_1056_, lean_object* v_fileMap_x3f_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1063_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_a_1068_; size_t v_sz_1086_; size_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___y_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v_sz_1086_ = lean_array_size(v_blocks_1056_);
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1086_, v___x_1087_, v_blocks_1056_);
v___x_1089_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1089_, 0, v___x_1088_);
v___x_1090_ = 1;
v___x_1091_ = lean_box(v___x_1090_);
v___y_1092_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1092_, 0, v_fileMap_x3f_1057_);
lean_closure_set(v___y_1092_, 1, v_declName_1054_);
lean_closure_set(v___y_1092_, 2, v_binders_1055_);
lean_closure_set(v___y_1092_, 3, v___x_1089_);
lean_closure_set(v___y_1092_, 4, v___x_1091_);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1093_, v___y_1092_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1063_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = l_Lean_Core_setMessageLog___redArg(v_a_1066_, v_a_1063_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; lean_object* v___x_1100_; size_t v_sz_1101_; lean_object* v___x_1102_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = l_Lean_MessageLog_toArray(v_a_1097_);
lean_dec(v_a_1097_);
v___x_1100_ = lean_box(0);
v_sz_1101_ = lean_array_size(v___x_1099_);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1099_, v_sz_1101_, v___x_1087_, v___x_1100_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec_ref(v___x_1099_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1127_; 
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v___x_1102_, 0);
lean_dec(v_unused_1128_);
v___x_1104_ = v___x_1102_;
v_isShared_1105_ = v_isSharedCheck_1127_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v___x_1102_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1127_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1126_; 
v_fst_1106_ = lean_ctor_get(v_a_1095_, 0);
v_snd_1107_ = lean_ctor_get(v_a_1095_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1095_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1109_ = v_a_1095_;
v_isShared_1110_ = v_isSharedCheck_1126_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_inc(v_fst_1106_);
lean_dec(v_a_1095_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1126_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1125_; 
v_fst_1111_ = lean_ctor_get(v_fst_1106_, 0);
v_snd_1112_ = lean_ctor_get(v_fst_1106_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_fst_1106_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1114_ = v_fst_1106_;
v_isShared_1115_ = v_isSharedCheck_1125_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v_fst_1106_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1125_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_fst_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_snd_1112_);
v___x_1117_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1117_);
v___x_1119_ = v___x_1109_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_snd_1107_);
v___x_1119_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1121_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1119_);
v___x_1121_ = v___x_1104_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_a_1095_);
v_a_1129_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1102_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1102_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_a_1097_);
lean_dec(v_a_1095_);
v_a_1137_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1098_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1098_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1145_; 
lean_dec(v_a_1095_);
v_a_1145_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1096_, 1);
v_a_1068_ = v_a_1145_;
goto v___jp_1067_;
}
}
else
{
lean_object* v_a_1146_; 
v_a_1146_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1094_, 1);
v_a_1068_ = v_a_1146_;
goto v___jp_1067_;
}
v___jp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Core_setMessageLog___redArg(v_a_1066_, v_a_1063_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v___x_1069_, 0);
lean_dec(v_unused_1077_);
v___x_1071_ = v___x_1069_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v___x_1069_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
lean_ctor_set_tag(v___x_1071_, 1);
lean_ctor_set(v___x_1071_, 0, v_a_1068_);
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1068_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec_ref(v_a_1068_);
v_a_1078_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1069_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1069_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_fileMap_x3f_1057_);
lean_dec_ref(v_blocks_1056_);
lean_dec(v_binders_1055_);
lean_dec(v_declName_1054_);
v_a_1147_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1065_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1065_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1155_, lean_object* v_binders_1156_, lean_object* v_blocks_1157_, lean_object* v_fileMap_x3f_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1155_, v_binders_1156_, v_blocks_1157_, v_fileMap_x3f_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1167_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_flag_boxed_1184_; lean_object* v_res_1185_; 
v_flag_boxed_1184_ = lean_unbox(v_flag_1176_);
v_res_1185_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1184_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1186_, uint8_t v_flag_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_flag_1198_, lean_object* v_x_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_flag_boxed_1207_; lean_object* v_res_1208_; 
v_flag_boxed_1207_ = lean_unbox(v_flag_1198_);
v_res_1208_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1197_, v_flag_boxed_1207_, v_x_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1209_, lean_object* v_msgData_1210_, uint8_t v_severity_1211_, uint8_t v_isSilent_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1209_, v_msgData_1210_, v_severity_1211_, v_isSilent_1212_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1221_, lean_object* v_msgData_1222_, lean_object* v_severity_1223_, lean_object* v_isSilent_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
uint8_t v_severity_boxed_1232_; uint8_t v_isSilent_boxed_1233_; lean_object* v_res_1234_; 
v_severity_boxed_1232_ = lean_unbox(v_severity_1223_);
v_isSilent_boxed_1233_ = lean_unbox(v_isSilent_1224_);
v_res_1234_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1221_, v_msgData_1222_, v_severity_boxed_1232_, v_isSilent_boxed_1233_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v_ref_1221_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1235_, uint8_t v_severity_1236_, uint8_t v_isSilent_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_ref_1243_; lean_object* v___x_1244_; 
v_ref_1243_ = lean_ctor_get(v___y_1240_, 2);
v___x_1244_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1243_, v_msgData_1235_, v_severity_1236_, v_isSilent_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1245_, lean_object* v_severity_1246_, lean_object* v_isSilent_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v_severity_boxed_1253_; uint8_t v_isSilent_boxed_1254_; lean_object* v_res_1255_; 
v_severity_boxed_1253_ = lean_unbox(v_severity_1246_);
v_isSilent_boxed_1254_ = lean_unbox(v_isSilent_1247_);
v_res_1255_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1245_, v_severity_boxed_1253_, v_isSilent_boxed_1254_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = 2;
v___x_1265_ = 0;
v___x_1266_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1256_, v___x_1264_, v___x_1265_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1276_, size_t v_sz_1277_, size_t v_i_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_usize_dec_lt(v_i_1278_, v_sz_1277_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_b_1279_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v_snd_1290_; lean_object* v_snd_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1289_ = lean_array_uget_borrowed(v_as_1276_, v_i_1278_);
v_snd_1290_ = lean_ctor_get(v_a_1289_, 1);
v_snd_1291_ = lean_ctor_get(v_snd_1290_, 1);
v___x_1292_ = lean_box(0);
lean_inc(v_snd_1291_);
v___x_1293_ = l_Lean_Parser_Error_toString(v_snd_1291_);
v___x_1294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
v___x_1295_ = l_Lean_MessageData_ofFormat(v___x_1294_);
v___x_1296_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1295_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1296_) == 0)
{
size_t v___x_1297_; size_t v___x_1298_; 
lean_dec_ref_known(v___x_1296_, 1);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1278_, v___x_1297_);
v_i_1278_ = v___x_1298_;
v_b_1279_ = v___x_1292_;
goto _start;
}
else
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1300_, lean_object* v_sz_1301_, lean_object* v_i_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
size_t v_sz_boxed_1311_; size_t v_i_boxed_1312_; lean_object* v_res_1313_; 
v_sz_boxed_1311_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v_i_boxed_1312_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1300_, v_sz_boxed_1311_, v_i_boxed_1312_, v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec_ref(v_as_1300_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1332_, lean_object* v_binders_1333_, lean_object* v_docComment_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v_toCold_1343_; lean_object* v_env_1344_; lean_object* v_fileName_1345_; lean_object* v_currNamespace_1346_; lean_object* v_openDecls_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1342_ = lean_st_ref_get(v_a_1340_);
v_toCold_1343_ = lean_ctor_get(v_a_1339_, 0);
v_env_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_ref_n(v_env_1344_, 2);
lean_dec(v___x_1342_);
v_fileName_1345_ = lean_ctor_get(v_toCold_1343_, 0);
v_currNamespace_1346_ = lean_ctor_get(v_toCold_1343_, 4);
v_openDecls_1347_ = lean_ctor_get(v_toCold_1343_, 5);
v___x_1348_ = lean_string_utf8_byte_size(v_docComment_1334_);
lean_inc_ref_n(v_docComment_1334_, 2);
v___x_1349_ = l_Lean_FileMap_ofString(v_docComment_1334_);
lean_inc_ref(v___x_1349_);
lean_inc_ref(v_fileName_1345_);
v___x_1350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1350_, 0, v_docComment_1334_);
lean_ctor_set(v___x_1350_, 1, v_fileName_1345_);
lean_ctor_set(v___x_1350_, 2, v___x_1349_);
lean_ctor_set(v___x_1350_, 3, v___x_1348_);
v___x_1351_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1339_);
lean_inc(v_openDecls_1347_);
lean_inc(v_currNamespace_1346_);
v___x_1352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1352_, 0, v_env_1344_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
lean_ctor_set(v___x_1352_, 2, v_currNamespace_1346_);
lean_ctor_set(v___x_1352_, 3, v_openDecls_1347_);
v___x_1353_ = l_Lean_Parser_mkParserState(v_docComment_1334_);
lean_dec_ref(v_docComment_1334_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1356_ = l_Lean_Parser_getTokenTable(v_env_1344_);
v___x_1357_ = l_Lean_Parser_ParserFn_run(v___x_1355_, v___x_1350_, v___x_1352_, v___x_1356_, v___x_1353_);
lean_inc_ref(v___x_1357_);
v___x_1358_ = l_Lean_Parser_ParserState_allErrors(v___x_1357_);
v___x_1359_ = lean_array_get_size(v___x_1358_);
v___x_1360_ = lean_nat_dec_eq(v___x_1359_, v___x_1354_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; size_t v_sz_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
lean_dec_ref(v___x_1357_);
lean_dec_ref(v___x_1349_);
lean_dec(v_binders_1333_);
lean_dec(v_declName_1332_);
v___x_1361_ = lean_box(0);
v_sz_1362_ = lean_array_size(v___x_1358_);
v___x_1363_ = ((size_t)0ULL);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1358_, v_sz_1362_, v___x_1363_, v___x_1361_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1372_; 
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1364_, 0);
lean_dec(v_unused_1373_);
v___x_1366_ = v___x_1364_;
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v___x_1364_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1372_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_a_1374_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1364_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1364_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_stxStack_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v___x_1358_);
v_stxStack_1382_ = lean_ctor_get(v___x_1357_, 0);
lean_inc_ref(v_stxStack_1382_);
lean_dec_ref(v___x_1357_);
v___x_1383_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1382_);
lean_dec_ref(v_stxStack_1382_);
v___x_1384_ = l_Lean_TSyntax_getVersoBlocks(v___x_1383_);
lean_dec(v___x_1383_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1349_);
v___x_1386_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1332_, v_binders_1333_, v___x_1384_, v___x_1385_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1387_, lean_object* v_binders_1388_, lean_object* v_docComment_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_versoDocStringOfText(v_declName_1387_, v_binders_1388_, v_docComment_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1398_, uint8_t v_severity_1399_, uint8_t v_isSilent_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1398_, v_severity_1399_, v_isSilent_1400_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1409_, lean_object* v_severity_1410_, lean_object* v_isSilent_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v_severity_boxed_1419_; uint8_t v_isSilent_boxed_1420_; lean_object* v_res_1421_; 
v_severity_boxed_1419_ = lean_unbox(v_severity_1410_);
v_isSilent_boxed_1420_ = lean_unbox(v_isSilent_1411_);
v_res_1421_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1409_, v_severity_boxed_1419_, v_isSilent_boxed_1420_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1431_, lean_object* v_binders_1432_, lean_object* v_docComment_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1433_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; lean_object* v_body_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
lean_dec_ref_known(v___x_1441_, 1);
v___x_1442_ = lean_unsigned_to_nat(1u);
v_body_1443_ = l_Lean_Syntax_getArg(v_docComment_1433_, v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1445_ = l_Lean_Syntax_isOfKind(v_body_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = l_Lean_TSyntax_getDocString(v_docComment_1433_);
v___x_1447_ = l_Lean_versoDocStringOfText(v_declName_1431_, v_binders_1432_, v___x_1446_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; lean_object* v_markup_1449_; 
v___x_1448_ = l_Lean_VersoDocstringView_of(v_docComment_1433_);
v_markup_1449_ = lean_ctor_get(v___x_1448_, 1);
lean_inc_ref(v_markup_1449_);
lean_dec_ref(v___x_1448_);
if (lean_obj_tag(v_markup_1449_) == 0)
{
lean_object* v_doc_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_doc_1450_ = lean_ctor_get(v_markup_1449_, 0);
lean_inc(v_doc_1450_);
lean_dec_ref_known(v_markup_1449_, 1);
v___x_1451_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1450_);
lean_dec(v_doc_1450_);
v___x_1452_ = lean_box(0);
v___x_1453_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1431_, v_binders_1432_, v___x_1451_, v___x_1452_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1453_;
}
else
{
lean_object* v_text_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_text_1454_ = lean_ctor_get(v_markup_1449_, 0);
lean_inc(v_text_1454_);
lean_dec_ref_known(v_markup_1449_, 1);
v___x_1455_ = l_Lean_Syntax_getAtomVal(v_text_1454_);
lean_dec(v_text_1454_);
v___x_1456_ = l_Lean_versoDocStringOfText(v_declName_1431_, v_binders_1432_, v___x_1455_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
return v___x_1456_;
}
}
}
else
{
lean_object* v___x_1457_; 
lean_dec_ref_known(v___x_1441_, 1);
v___x_1457_ = l_Lean_parseVersoDocString(v_docComment_1433_, v_a_1438_, v_a_1439_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1505_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1505_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1505_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
if (lean_obj_tag(v_a_1458_) == 1)
{
lean_object* v_val_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
lean_del_object(v___x_1460_);
v_val_1462_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_val_1462_);
lean_dec_ref_known(v_a_1458_, 1);
v___x_1463_ = l_Lean_TSyntax_getVersoBlocks(v_val_1462_);
lean_dec(v_val_1462_);
v___x_1464_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1464_, 0, v___x_1463_);
v___x_1465_ = 0;
v___x_1466_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1431_, v_binders_1432_, v___x_1464_, v___x_1465_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1492_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1492_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1492_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v_fst_1471_; lean_object* v_snd_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1491_; 
v_fst_1471_ = lean_ctor_get(v_a_1467_, 0);
v_snd_1472_ = lean_ctor_get(v_a_1467_, 1);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_a_1467_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1474_ = v_a_1467_;
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snd_1472_);
lean_inc(v_fst_1471_);
lean_dec(v_a_1467_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_fst_1476_; lean_object* v_snd_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1490_; 
v_fst_1476_ = lean_ctor_get(v_fst_1471_, 0);
v_snd_1477_ = lean_ctor_get(v_fst_1471_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_fst_1471_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1479_ = v_fst_1471_;
v_isShared_1480_ = v_isSharedCheck_1490_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_snd_1477_);
lean_inc(v_fst_1476_);
lean_dec(v_fst_1471_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1490_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_fst_1476_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_snd_1477_);
v___x_1482_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v___x_1482_);
v___x_1484_ = v___x_1474_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_snd_1472_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1484_);
v___x_1486_ = v___x_1469_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_a_1493_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1466_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1466_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
lean_dec(v_a_1458_);
lean_dec(v_binders_1432_);
lean_dec(v_declName_1431_);
v___x_1501_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1501_);
v___x_1503_ = v___x_1460_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_binders_1432_);
lean_dec(v_declName_1431_);
v_a_1506_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1457_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1457_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1514_, lean_object* v_binders_1515_, lean_object* v_docComment_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_versoDocString(v_declName_1514_, v_binders_1515_, v_docComment_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_docComment_1516_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1525_, lean_object* v_doc_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v_val_1542_; lean_object* v_env_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1534_ = lean_st_ref_get(v_a_1532_);
v_env_1544_ = lean_ctor_get(v___x_1534_, 0);
lean_inc_ref(v_env_1544_);
lean_dec(v___x_1534_);
v___x_1545_ = l_Lean_getMainVersoModuleDocs(v_env_1544_);
v___x_1546_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1545_);
lean_dec_ref(v___x_1545_);
if (lean_obj_tag(v___x_1546_) == 0)
{
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1526_);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___y_1536_ = v___x_1547_;
v___y_1537_ = v___x_1548_;
goto v___jp_1535_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___x_1546_, 1);
v_val_1542_ = v_val_1549_;
goto v___jp_1541_;
}
}
else
{
lean_object* v_val_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_val_1550_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1550_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_nat_add(v_val_1550_, v___x_1551_);
lean_dec(v_val_1550_);
v_val_1542_ = v___x_1552_;
goto v___jp_1541_;
}
v___jp_1535_:
{
lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1538_, 0, v_range_1525_);
lean_closure_set(v___x_1538_, 1, v___y_1536_);
lean_closure_set(v___x_1538_, 2, v___y_1537_);
v___x_1539_ = 0;
v___x_1540_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1538_, v___x_1539_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1540_;
}
v___jp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1526_);
v___y_1536_ = v___x_1543_;
v___y_1537_ = v_val_1542_;
goto v___jp_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1553_, lean_object* v_doc_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_versoModDocString(v_range_1553_, v_doc_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_doc_1554_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1572_, lean_object* v_docComment_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1582_ = l_Lean_versoDocStringOfText(v_declName_1572_, v___x_1581_, v_docComment_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1583_, lean_object* v_docComment_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_versoDocStringFromString(v_declName_1583_, v_docComment_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1593_, lean_object* v_declName_1594_, lean_object* v_env_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = l_Lean_docStringExt;
v___x_1597_ = l_String_removeLeadingSpaces(v_docString_1593_);
v___x_1598_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1596_, v_env_1595_, v_declName_1594_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1599_, lean_object* v_modifyEnv_1600_, lean_object* v_docString_1601_){
_start:
{
lean_object* v___f_1602_; lean_object* v___x_1603_; 
v___f_1602_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1602_, 0, v_docString_1601_);
lean_closure_set(v___f_1602_, 1, v_declName_1599_);
v___x_1603_ = lean_apply_1(v_modifyEnv_1600_, v___f_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_docComment_1606_, lean_object* v_toBind_1607_, lean_object* v___f_1608_, lean_object* v_____r_1609_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = l_Lean_getDocStringText___redArg(v_inst_1604_, v_inst_1605_, v_docComment_1606_);
v___x_1611_ = lean_apply_4(v_toBind_1607_, lean_box(0), lean_box(0), v___x_1610_, v___f_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_docComment_1617_, lean_object* v_toBind_1618_, lean_object* v___f_1619_, lean_object* v_____r_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_validateDocComment___redArg(v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_inst_1616_, v_docComment_1617_);
v___x_1622_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1621_, v___f_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_docComment_1628_, lean_object* v_toBind_1629_, lean_object* v___f_1630_, lean_object* v_____r_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_docComment_1628_, v_toBind_1629_, v___f_1630_, v_____r_1631_);
lean_dec(v_docComment_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1633_, lean_object* v_____r_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_apply_1(v___f_1633_, v_____r_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_1642_, lean_object* v_declName_1643_, uint8_t v___x_1644_, lean_object* v_inst_1645_, lean_object* v_inst_1646_, lean_object* v_toBind_1647_, lean_object* v___f_1648_, lean_object* v_____do__lift_1649_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1649_, v_declName_1643_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_dec(v___f_1648_);
lean_dec(v_toBind_1647_);
lean_dec_ref(v_inst_1646_);
lean_dec_ref(v_inst_1645_);
lean_dec(v_declName_1643_);
goto v___jp_1650_;
}
else
{
lean_dec_ref_known(v___x_1653_, 1);
if (v___x_1644_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v___f_1642_);
v___x_1654_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1655_ = l_Lean_MessageData_ofConstName(v_declName_1643_, v___x_1644_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = l_Lean_throwError___redArg(v_inst_1645_, v_inst_1646_, v___x_1658_);
v___x_1660_ = lean_apply_4(v_toBind_1647_, lean_box(0), lean_box(0), v___x_1659_, v___f_1648_);
return v___x_1660_;
}
else
{
lean_dec(v___f_1648_);
lean_dec(v_toBind_1647_);
lean_dec_ref(v_inst_1646_);
lean_dec_ref(v_inst_1645_);
lean_dec(v_declName_1643_);
goto v___jp_1650_;
}
}
v___jp_1650_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_apply_1(v___f_1642_, v___x_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_1661_, lean_object* v_declName_1662_, lean_object* v___x_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_toBind_1666_, lean_object* v___f_1667_, lean_object* v_____do__lift_1668_){
_start:
{
uint8_t v___x_247__boxed_1669_; lean_object* v_res_1670_; 
v___x_247__boxed_1669_ = lean_unbox(v___x_1663_);
v_res_1670_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1661_, v_declName_1662_, v___x_247__boxed_1669_, v_inst_1664_, v_inst_1665_, v_toBind_1666_, v___f_1667_, v_____do__lift_1668_);
lean_dec_ref(v_____do__lift_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_declName_1678_, lean_object* v_docComment_1679_){
_start:
{
lean_object* v_toApplicative_1680_; lean_object* v_toBind_1681_; lean_object* v_toPure_1682_; uint8_t v___x_1683_; 
v_toApplicative_1680_ = lean_ctor_get(v_inst_1671_, 0);
v_toBind_1681_ = lean_ctor_get(v_inst_1671_, 1);
lean_inc(v_toBind_1681_);
v_toPure_1682_ = lean_ctor_get(v_toApplicative_1680_, 1);
v___x_1683_ = l_Lean_Name_isAnonymous(v_declName_1678_);
if (v___x_1683_ == 0)
{
lean_object* v_getEnv_1684_; lean_object* v_modifyEnv_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; 
v_getEnv_1684_ = lean_ctor_get(v_inst_1674_, 0);
lean_inc(v_getEnv_1684_);
v_modifyEnv_1685_ = lean_ctor_get(v_inst_1674_, 1);
lean_inc(v_modifyEnv_1685_);
lean_dec_ref(v_inst_1674_);
lean_inc(v_declName_1678_);
v___f_1686_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1686_, 0, v_declName_1678_);
lean_closure_set(v___f_1686_, 1, v_modifyEnv_1685_);
lean_inc_n(v_toBind_1681_, 3);
lean_inc(v_docComment_1679_);
lean_inc_ref(v_inst_1675_);
lean_inc_ref_n(v_inst_1671_, 2);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1687_, 0, v_inst_1671_);
lean_closure_set(v___f_1687_, 1, v_inst_1675_);
lean_closure_set(v___f_1687_, 2, v_docComment_1679_);
lean_closure_set(v___f_1687_, 3, v_toBind_1681_);
lean_closure_set(v___f_1687_, 4, v___f_1686_);
v___f_1688_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1688_, 0, v_inst_1671_);
lean_closure_set(v___f_1688_, 1, v_inst_1672_);
lean_closure_set(v___f_1688_, 2, v_inst_1676_);
lean_closure_set(v___f_1688_, 3, v_inst_1677_);
lean_closure_set(v___f_1688_, 4, v_inst_1673_);
lean_closure_set(v___f_1688_, 5, v_docComment_1679_);
lean_closure_set(v___f_1688_, 6, v_toBind_1681_);
lean_closure_set(v___f_1688_, 7, v___f_1687_);
lean_inc_ref(v___f_1688_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1689_, 0, v___f_1688_);
v___x_1690_ = lean_box(v___x_1683_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1691_, 0, v___f_1688_);
lean_closure_set(v___f_1691_, 1, v_declName_1678_);
lean_closure_set(v___f_1691_, 2, v___x_1690_);
lean_closure_set(v___f_1691_, 3, v_inst_1671_);
lean_closure_set(v___f_1691_, 4, v_inst_1675_);
lean_closure_set(v___f_1691_, 5, v_toBind_1681_);
lean_closure_set(v___f_1691_, 6, v___f_1689_);
v___x_1692_ = lean_apply_4(v_toBind_1681_, lean_box(0), lean_box(0), v_getEnv_1684_, v___f_1691_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_inc(v_toPure_1682_);
lean_dec(v_toBind_1681_);
lean_dec(v_docComment_1679_);
lean_dec(v_declName_1678_);
lean_dec(v_inst_1677_);
lean_dec_ref(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec_ref(v_inst_1673_);
lean_dec(v_inst_1672_);
lean_dec_ref(v_inst_1671_);
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_apply_2(v_toPure_1682_, lean_box(0), v___x_1693_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1695_, lean_object* v_inst_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_declName_1703_, lean_object* v_docComment_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_addMarkdownDocString___redArg(v_inst_1696_, v_inst_1697_, v_inst_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_, v_inst_1702_, v_declName_1703_, v_docComment_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_declName_1706_, lean_object* v_x1_1707_, lean_object* v_x2_1708_){
_start:
{
lean_object* v_index_1709_; lean_object* v_sourceString_1710_; lean_object* v_imports_1711_; lean_object* v_currNamespace_1712_; lean_object* v_openDecls_1713_; lean_object* v_options_1714_; lean_object* v_check_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1728_; 
v_index_1709_ = lean_ctor_get(v_x2_1708_, 1);
v_sourceString_1710_ = lean_ctor_get(v_x2_1708_, 2);
v_imports_1711_ = lean_ctor_get(v_x2_1708_, 3);
v_currNamespace_1712_ = lean_ctor_get(v_x2_1708_, 4);
v_openDecls_1713_ = lean_ctor_get(v_x2_1708_, 5);
v_options_1714_ = lean_ctor_get(v_x2_1708_, 6);
v_check_1715_ = lean_ctor_get(v_x2_1708_, 7);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_x2_1708_);
if (v_isSharedCheck_1728_ == 0)
{
lean_object* v_unused_1729_; 
v_unused_1729_ = lean_ctor_get(v_x2_1708_, 0);
lean_dec(v_unused_1729_);
v___x_1717_ = v_x2_1708_;
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_check_1715_);
lean_inc(v_options_1714_);
lean_inc(v_openDecls_1713_);
lean_inc(v_currNamespace_1712_);
lean_inc(v_imports_1711_);
lean_inc(v_sourceString_1710_);
lean_inc(v_index_1709_);
lean_dec(v_x2_1708_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v_toEnvExtension_1720_; lean_object* v_asyncMode_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1719_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1720_ = lean_ctor_get(v___x_1719_, 0);
v_asyncMode_1721_ = lean_ctor_get(v_toEnvExtension_1720_, 2);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_declName_1706_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1722_);
v___x_1724_ = v___x_1717_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_index_1709_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_sourceString_1710_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_imports_1711_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v_currNamespace_1712_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v_openDecls_1713_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v_options_1714_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_check_1715_);
v___x_1724_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(0);
v___x_1726_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1719_, v_x1_1707_, v___x_1724_, v_asyncMode_1721_, v___x_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1749_, lean_object* v_docs_1750_, lean_object* v_deferred_1751_, lean_object* v___f_1752_, lean_object* v_env_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v_env_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1754_ = l_Lean_versoDocStringExt;
v_env_1755_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1754_, v_env_1753_, v_declName_1749_, v_docs_1750_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = lean_array_get_size(v_deferred_1751_);
v___x_1758_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_1759_ = lean_nat_dec_lt(v___x_1756_, v___x_1757_);
if (v___x_1759_ == 0)
{
lean_dec_ref(v___f_1752_);
lean_dec_ref(v_deferred_1751_);
return v_env_1755_;
}
else
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_nat_dec_le(v___x_1757_, v___x_1757_);
if (v___x_1760_ == 0)
{
if (v___x_1759_ == 0)
{
lean_dec_ref(v___f_1752_);
lean_dec_ref(v_deferred_1751_);
return v_env_1755_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1757_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1758_, v___f_1752_, v_deferred_1751_, v___x_1761_, v___x_1762_, v_env_1755_);
return v___x_1763_;
}
}
else
{
size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = lean_usize_of_nat(v___x_1757_);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1758_, v___f_1752_, v_deferred_1751_, v___x_1764_, v___x_1765_, v_env_1755_);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_modifyEnv_1767_, lean_object* v___f_1768_, lean_object* v_____r_1769_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_apply_1(v_modifyEnv_1767_, v___f_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_declName_1773_, lean_object* v_modifyEnv_1774_, lean_object* v___f_1775_, uint8_t v___x_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_toBind_1779_, lean_object* v___f_1780_, lean_object* v_____do__lift_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1781_, v_declName_1773_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v___x_1783_; 
lean_dec(v___f_1780_);
lean_dec(v_toBind_1779_);
lean_dec_ref(v_inst_1778_);
lean_dec_ref(v_inst_1777_);
lean_dec(v_declName_1773_);
v___x_1783_ = lean_apply_1(v_modifyEnv_1774_, v___f_1775_);
return v___x_1783_;
}
else
{
lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1800_; 
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v___x_1782_, 0);
lean_dec(v_unused_1801_);
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1800_;
goto v_resetjp_1784_;
}
else
{
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1800_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
if (v___x_1776_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec_ref(v___f_1775_);
lean_dec(v_modifyEnv_1774_);
v___x_1787_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_1788_ = 1;
v___x_1789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1773_, v___x_1788_);
v___x_1790_ = lean_string_append(v___x_1787_, v___x_1789_);
lean_dec_ref(v___x_1789_);
v___x_1791_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 3);
lean_ctor_set(v___x_1785_, 0, v___x_1792_);
v___x_1794_ = v___x_1785_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = l_Lean_MessageData_ofFormat(v___x_1794_);
v___x_1796_ = l_Lean_throwError___redArg(v_inst_1777_, v_inst_1778_, v___x_1795_);
v___x_1797_ = lean_apply_4(v_toBind_1779_, lean_box(0), lean_box(0), v___x_1796_, v___f_1780_);
return v___x_1797_;
}
}
else
{
lean_object* v___x_1799_; 
lean_del_object(v___x_1785_);
lean_dec(v___f_1780_);
lean_dec(v_toBind_1779_);
lean_dec_ref(v_inst_1778_);
lean_dec_ref(v_inst_1777_);
lean_dec(v_declName_1773_);
v___x_1799_ = lean_apply_1(v_modifyEnv_1774_, v___f_1775_);
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3___boxed(lean_object* v_declName_1802_, lean_object* v_modifyEnv_1803_, lean_object* v___f_1804_, lean_object* v___x_1805_, lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_toBind_1808_, lean_object* v___f_1809_, lean_object* v_____do__lift_1810_){
_start:
{
uint8_t v___x_374__boxed_1811_; lean_object* v_res_1812_; 
v___x_374__boxed_1811_ = lean_unbox(v___x_1805_);
v_res_1812_ = l_Lean_addVersoDocStringCore___redArg___lam__3(v_declName_1802_, v_modifyEnv_1803_, v___f_1804_, v___x_374__boxed_1811_, v_inst_1806_, v_inst_1807_, v_toBind_1808_, v___f_1809_, v_____do__lift_1810_);
lean_dec_ref(v_____do__lift_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_declName_1816_, lean_object* v_docs_1817_, lean_object* v_deferred_1818_){
_start:
{
lean_object* v_toApplicative_1819_; lean_object* v_toBind_1820_; lean_object* v_toPure_1821_; uint8_t v___x_1822_; 
v_toApplicative_1819_ = lean_ctor_get(v_inst_1813_, 0);
v_toBind_1820_ = lean_ctor_get(v_inst_1813_, 1);
lean_inc(v_toBind_1820_);
v_toPure_1821_ = lean_ctor_get(v_toApplicative_1819_, 1);
v___x_1822_ = l_Lean_Name_isAnonymous(v_declName_1816_);
if (v___x_1822_ == 0)
{
lean_object* v_getEnv_1823_; lean_object* v_modifyEnv_1824_; lean_object* v___f_1825_; lean_object* v___f_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v_getEnv_1823_ = lean_ctor_get(v_inst_1814_, 0);
lean_inc(v_getEnv_1823_);
v_modifyEnv_1824_ = lean_ctor_get(v_inst_1814_, 1);
lean_inc_n(v_modifyEnv_1824_, 2);
lean_dec_ref(v_inst_1814_);
lean_inc_n(v_declName_1816_, 2);
v___f_1825_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1825_, 0, v_declName_1816_);
v___f_1826_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1826_, 0, v_declName_1816_);
lean_closure_set(v___f_1826_, 1, v_docs_1817_);
lean_closure_set(v___f_1826_, 2, v_deferred_1818_);
lean_closure_set(v___f_1826_, 3, v___f_1825_);
lean_inc_ref(v___f_1826_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1827_, 0, v_modifyEnv_1824_);
lean_closure_set(v___f_1827_, 1, v___f_1826_);
v___x_1828_ = lean_box(v___x_1822_);
lean_inc(v_toBind_1820_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1829_, 0, v_declName_1816_);
lean_closure_set(v___f_1829_, 1, v_modifyEnv_1824_);
lean_closure_set(v___f_1829_, 2, v___f_1826_);
lean_closure_set(v___f_1829_, 3, v___x_1828_);
lean_closure_set(v___f_1829_, 4, v_inst_1813_);
lean_closure_set(v___f_1829_, 5, v_inst_1815_);
lean_closure_set(v___f_1829_, 6, v_toBind_1820_);
lean_closure_set(v___f_1829_, 7, v___f_1827_);
v___x_1830_ = lean_apply_4(v_toBind_1820_, lean_box(0), lean_box(0), v_getEnv_1823_, v___f_1829_);
return v___x_1830_;
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_inc(v_toPure_1821_);
lean_dec(v_toBind_1820_);
lean_dec_ref(v_deferred_1818_);
lean_dec_ref(v_docs_1817_);
lean_dec(v_declName_1816_);
lean_dec_ref(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
v___x_1831_ = lean_box(0);
v___x_1832_ = lean_apply_2(v_toPure_1821_, lean_box(0), v___x_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_declName_1838_, lean_object* v_docs_1839_, lean_object* v_deferred_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1834_, v_inst_1835_, v_inst_1837_, v_declName_1838_, v_docs_1839_, v_deferred_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_declName_1847_, lean_object* v_docs_1848_, lean_object* v_deferred_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_addVersoDocStringCore(v_m_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_inst_1846_, v_declName_1847_, v_docs_1848_, v_deferred_1849_);
lean_dec(v_inst_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_size_1851_, lean_object* v_x1_1852_, lean_object* v_x2_1853_){
_start:
{
lean_object* v_index_1854_; lean_object* v_sourceString_1855_; lean_object* v_imports_1856_; lean_object* v_currNamespace_1857_; lean_object* v_openDecls_1858_; lean_object* v_options_1859_; lean_object* v_check_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1873_; 
v_index_1854_ = lean_ctor_get(v_x2_1853_, 1);
v_sourceString_1855_ = lean_ctor_get(v_x2_1853_, 2);
v_imports_1856_ = lean_ctor_get(v_x2_1853_, 3);
v_currNamespace_1857_ = lean_ctor_get(v_x2_1853_, 4);
v_openDecls_1858_ = lean_ctor_get(v_x2_1853_, 5);
v_options_1859_ = lean_ctor_get(v_x2_1853_, 6);
v_check_1860_ = lean_ctor_get(v_x2_1853_, 7);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_x2_1853_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_x2_1853_, 0);
lean_dec(v_unused_1874_);
v___x_1862_ = v_x2_1853_;
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_check_1860_);
lean_inc(v_options_1859_);
lean_inc(v_openDecls_1858_);
lean_inc(v_currNamespace_1857_);
lean_inc(v_imports_1856_);
lean_inc(v_sourceString_1855_);
lean_inc(v_index_1854_);
lean_dec(v_x2_1853_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v_toEnvExtension_1865_; lean_object* v_asyncMode_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1864_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1865_ = lean_ctor_get(v___x_1864_, 0);
v_asyncMode_1866_ = lean_ctor_get(v_toEnvExtension_1865_, 2);
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_size_1851_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1867_);
v___x_1869_ = v___x_1862_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_index_1854_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_sourceString_1855_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_imports_1856_);
lean_ctor_set(v_reuseFailAlloc_1872_, 4, v_currNamespace_1857_);
lean_ctor_set(v_reuseFailAlloc_1872_, 5, v_openDecls_1858_);
lean_ctor_set(v_reuseFailAlloc_1872_, 6, v_options_1859_);
lean_ctor_set(v_reuseFailAlloc_1872_, 7, v_check_1860_);
v___x_1869_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_box(0);
v___x_1871_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1864_, v_x1_1852_, v___x_1869_, v_asyncMode_1866_, v___x_1870_);
return v___x_1871_;
}
}
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__0));
v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_docs_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_deferred_1881_, lean_object* v_inst_1882_, lean_object* v___f_1883_, lean_object* v_____do__lift_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1884_, v_docs_1878_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec_ref(v___f_1883_);
lean_dec_ref(v_inst_1882_);
lean_dec_ref(v_deferred_1881_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_1888_ = l_Lean_stringToMessageData(v_a_1886_);
v___x_1889_ = l_Lean_indentD(v___x_1888_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1887_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_throwError___redArg(v_inst_1879_, v_inst_1880_, v___x_1890_);
return v___x_1891_;
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
lean_dec_ref(v_inst_1880_);
lean_dec_ref(v_inst_1879_);
v_a_1892_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_array_get_size(v_deferred_1881_);
v___x_1895_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__1___closed__9));
v___x_1896_ = lean_nat_dec_lt(v___x_1893_, v___x_1894_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec_ref(v___f_1883_);
lean_dec_ref(v_deferred_1881_);
v___x_1897_ = l_Lean_setEnv___redArg(v_inst_1882_, v_a_1892_);
return v___x_1897_;
}
else
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_le(v___x_1894_, v___x_1894_);
if (v___x_1898_ == 0)
{
if (v___x_1896_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v___f_1883_);
lean_dec_ref(v_deferred_1881_);
v___x_1899_ = l_Lean_setEnv___redArg(v_inst_1882_, v_a_1892_);
return v___x_1899_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = ((size_t)0ULL);
v___x_1901_ = lean_usize_of_nat(v___x_1894_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1895_, v___f_1883_, v_deferred_1881_, v___x_1900_, v___x_1901_, v_a_1892_);
v___x_1903_ = l_Lean_setEnv___redArg(v_inst_1882_, v___x_1902_);
return v___x_1903_;
}
}
else
{
size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = lean_usize_of_nat(v___x_1894_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1895_, v___f_1883_, v_deferred_1881_, v___x_1904_, v___x_1905_, v_a_1892_);
v___x_1907_ = l_Lean_setEnv___redArg(v_inst_1882_, v___x_1906_);
return v___x_1907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(lean_object* v_docs_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_deferred_1911_, lean_object* v_inst_1912_, lean_object* v_toBind_1913_, lean_object* v_getEnv_1914_, lean_object* v_____do__lift_1915_){
_start:
{
lean_object* v___x_1916_; lean_object* v_size_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___x_1920_; 
v___x_1916_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1915_);
v_size_1917_ = lean_ctor_get(v___x_1916_, 2);
lean_inc(v_size_1917_);
lean_dec_ref(v___x_1916_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1918_, 0, v_size_1917_);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1919_, 0, v_docs_1908_);
lean_closure_set(v___f_1919_, 1, v_inst_1909_);
lean_closure_set(v___f_1919_, 2, v_inst_1910_);
lean_closure_set(v___f_1919_, 3, v_deferred_1911_);
lean_closure_set(v___f_1919_, 4, v_inst_1912_);
lean_closure_set(v___f_1919_, 5, v___f_1918_);
v___x_1920_ = lean_apply_4(v_toBind_1913_, lean_box(0), lean_box(0), v_getEnv_1914_, v___f_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_toBind_1926_, lean_object* v_getEnv_1927_, lean_object* v___f_1928_, lean_object* v_____do__lift_1929_){
_start:
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1930_ = l_Lean_getMainModuleDoc(v_____do__lift_1929_);
v___x_1931_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_1930_);
lean_dec_ref(v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v___f_1928_);
lean_dec(v_getEnv_1927_);
lean_dec(v_toBind_1926_);
v___x_1932_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_1933_ = l_Lean_throwError___redArg(v_inst_1924_, v_inst_1925_, v___x_1932_);
return v___x_1933_;
}
else
{
lean_object* v___x_1934_; 
lean_dec_ref(v_inst_1925_);
lean_dec_ref(v_inst_1924_);
v___x_1934_ = lean_apply_4(v_toBind_1926_, lean_box(0), lean_box(0), v_getEnv_1927_, v___f_1928_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_docs_1938_, lean_object* v_deferred_1939_){
_start:
{
lean_object* v_toBind_1940_; lean_object* v_getEnv_1941_; lean_object* v___f_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; 
v_toBind_1940_ = lean_ctor_get(v_inst_1935_, 1);
lean_inc_n(v_toBind_1940_, 3);
v_getEnv_1941_ = lean_ctor_get(v_inst_1936_, 0);
lean_inc_n(v_getEnv_1941_, 3);
lean_inc_ref(v_inst_1937_);
lean_inc_ref(v_inst_1935_);
v___f_1942_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1942_, 0, v_docs_1938_);
lean_closure_set(v___f_1942_, 1, v_inst_1935_);
lean_closure_set(v___f_1942_, 2, v_inst_1937_);
lean_closure_set(v___f_1942_, 3, v_deferred_1939_);
lean_closure_set(v___f_1942_, 4, v_inst_1936_);
lean_closure_set(v___f_1942_, 5, v_toBind_1940_);
lean_closure_set(v___f_1942_, 6, v_getEnv_1941_);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1943_, 0, v_inst_1935_);
lean_closure_set(v___f_1943_, 1, v_inst_1937_);
lean_closure_set(v___f_1943_, 2, v_toBind_1940_);
lean_closure_set(v___f_1943_, 3, v_getEnv_1941_);
lean_closure_set(v___f_1943_, 4, v___f_1942_);
v___x_1944_ = lean_apply_4(v_toBind_1940_, lean_box(0), lean_box(0), v_getEnv_1941_, v___f_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_docs_1950_, lean_object* v_deferred_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_1946_, v_inst_1947_, v_inst_1949_, v_docs_1950_, v_deferred_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_docs_1958_, lean_object* v_deferred_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_addVersoModDocStringCore(v_m_1953_, v_inst_1954_, v_inst_1955_, v_inst_1956_, v_inst_1957_, v_docs_1958_, v_deferred_1959_);
lean_dec(v_inst_1956_);
return v_res_1960_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_box(1);
v___x_1962_ = l_Lean_MessageData_ofFormat(v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2));
v___x_1967_ = l_Lean_MessageData_ofFormat(v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
if (lean_obj_tag(v_x_1969_) == 0)
{
return v_x_1968_;
}
else
{
lean_object* v_head_1970_; lean_object* v_tail_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1993_; 
v_head_1970_ = lean_ctor_get(v_x_1969_, 0);
v_tail_1971_ = lean_ctor_get(v_x_1969_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_x_1969_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1973_ = v_x_1969_;
v_isShared_1974_ = v_isSharedCheck_1993_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_tail_1971_);
lean_inc(v_head_1970_);
lean_dec(v_x_1969_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1993_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_before_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1991_; 
v_before_1975_ = lean_ctor_get(v_head_1970_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_head_1970_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_head_1970_, 1);
lean_dec(v_unused_1992_);
v___x_1977_ = v_head_1970_;
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_before_1975_);
lean_dec(v_head_1970_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_1979_);
lean_ctor_set(v___x_1977_, 0, v_x_1968_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_x_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 7);
lean_ctor_set(v___x_1973_, 1, v___x_1982_);
lean_ctor_set(v___x_1973_, 0, v___x_1981_);
v___x_1984_ = v___x_1973_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = l_Lean_MessageData_ofSyntax(v_before_1975_);
v___x_1986_ = l_Lean_indentD(v___x_1985_);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1984_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v_x_1968_ = v___x_1987_;
v_x_1969_ = v_tail_1971_;
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
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1));
v___x_1998_ = l_Lean_MessageData_ofFormat(v___x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object* v_msgData_1999_, lean_object* v_macroStack_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2003_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2001_);
v___x_2004_ = l_Lean_Elab_pp_macroStack;
v___x_2005_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2003_, v___x_2004_);
lean_dec_ref(v___x_2003_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v_macroStack_2000_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_msgData_1999_);
return v___x_2006_;
}
else
{
if (lean_obj_tag(v_macroStack_2000_) == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2007_, 0, v_msgData_1999_);
return v___x_2007_;
}
else
{
lean_object* v_head_2008_; lean_object* v_after_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2024_; 
v_head_2008_ = lean_ctor_get(v_macroStack_2000_, 0);
lean_inc(v_head_2008_);
v_after_2009_ = lean_ctor_get(v_head_2008_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_head_2008_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_head_2008_, 0);
lean_dec(v_unused_2025_);
v___x_2011_ = v_head_2008_;
v_isShared_2012_ = v_isSharedCheck_2024_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_after_2009_);
lean_dec(v_head_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2024_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2013_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 7);
lean_ctor_set(v___x_2011_, 1, v___x_2013_);
lean_ctor_set(v___x_2011_, 0, v_msgData_1999_);
v___x_2015_ = v___x_2011_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_msgData_1999_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_msgData_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2016_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = l_Lean_MessageData_ofSyntax(v_after_2009_);
v___x_2019_ = l_Lean_indentD(v___x_2018_);
v_msgData_2020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2020_, 0, v___x_2017_);
lean_ctor_set(v_msgData_2020_, 1, v___x_2019_);
v___x_2021_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(v_msgData_2020_, v_macroStack_2000_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2026_, lean_object* v_macroStack_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2026_, v_macroStack_2027_, v___y_2028_);
lean_dec_ref(v___y_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_ref_2039_; lean_object* v_macroStack_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2053_; 
v_ref_2039_ = lean_ctor_get(v___y_2036_, 2);
v_macroStack_2040_ = lean_ctor_get(v___y_2032_, 1);
v___x_2041_ = l_Lean_Elab_getBetterRef(v_ref_2039_, v_macroStack_2040_);
v___x_2042_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2031_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
lean_inc(v_macroStack_2040_);
v___x_2044_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_a_2043_, v_macroStack_2040_, v___y_2036_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2041_);
lean_ctor_set(v___x_2049_, 1, v_a_2045_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set_tag(v___x_2047_, 1);
lean_ctor_set(v___x_2047_, 0, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2063_, lean_object* v_as_2064_, size_t v_i_2065_, size_t v_stop_2066_, lean_object* v_b_2067_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_eq(v_i_2065_, v_stop_2066_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v_index_2070_; lean_object* v_sourceString_2071_; lean_object* v_imports_2072_; lean_object* v_currNamespace_2073_; lean_object* v_openDecls_2074_; lean_object* v_options_2075_; lean_object* v_check_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2092_; 
v___x_2069_ = lean_array_uget(v_as_2064_, v_i_2065_);
v_index_2070_ = lean_ctor_get(v___x_2069_, 1);
v_sourceString_2071_ = lean_ctor_get(v___x_2069_, 2);
v_imports_2072_ = lean_ctor_get(v___x_2069_, 3);
v_currNamespace_2073_ = lean_ctor_get(v___x_2069_, 4);
v_openDecls_2074_ = lean_ctor_get(v___x_2069_, 5);
v_options_2075_ = lean_ctor_get(v___x_2069_, 6);
v_check_2076_ = lean_ctor_get(v___x_2069_, 7);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v___x_2069_, 0);
lean_dec(v_unused_2093_);
v___x_2078_ = v___x_2069_;
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_check_2076_);
lean_inc(v_options_2075_);
lean_inc(v_openDecls_2074_);
lean_inc(v_currNamespace_2073_);
lean_inc(v_imports_2072_);
lean_inc(v_sourceString_2071_);
lean_inc(v_index_2070_);
lean_dec(v___x_2069_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v_toEnvExtension_2081_; lean_object* v_asyncMode_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2080_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2081_ = lean_ctor_get(v___x_2080_, 0);
v_asyncMode_2082_ = lean_ctor_get(v_toEnvExtension_2081_, 2);
lean_inc(v_declName_2063_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_declName_2063_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2083_);
v___x_2085_ = v___x_2078_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_index_2070_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v_sourceString_2071_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v_imports_2072_);
lean_ctor_set(v_reuseFailAlloc_2091_, 4, v_currNamespace_2073_);
lean_ctor_set(v_reuseFailAlloc_2091_, 5, v_openDecls_2074_);
lean_ctor_set(v_reuseFailAlloc_2091_, 6, v_options_2075_);
lean_ctor_set(v_reuseFailAlloc_2091_, 7, v_check_2076_);
v___x_2085_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2080_, v_b_2067_, v___x_2085_, v_asyncMode_2082_, v___x_2086_);
v___x_2088_ = ((size_t)1ULL);
v___x_2089_ = lean_usize_add(v_i_2065_, v___x_2088_);
v_i_2065_ = v___x_2089_;
v_b_2067_ = v___x_2087_;
goto _start;
}
}
}
else
{
lean_dec(v_declName_2063_);
return v_b_2067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2094_, lean_object* v_as_2095_, lean_object* v_i_2096_, lean_object* v_stop_2097_, lean_object* v_b_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2097_);
lean_dec(v_stop_2097_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2094_, v_as_2095_, v_i_boxed_2099_, v_stop_boxed_2100_, v_b_2098_);
lean_dec_ref(v_as_2095_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2107_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
lean_ctor_set(v___x_2107_, 2, v___x_2106_);
lean_ctor_set(v___x_2107_, 3, v___x_2106_);
lean_ctor_set(v___x_2107_, 4, v___x_2106_);
lean_ctor_set(v___x_2107_, 5, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2108_, lean_object* v_docs_2109_, lean_object* v_deferred_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2151_; lean_object* v___y_2152_; uint8_t v___x_2171_; 
v___x_2171_ = l_Lean_Name_isAnonymous(v_declName_2108_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v_env_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_st_ref_get(v___y_2116_);
v_env_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_ref(v_env_2173_);
lean_dec(v___x_2172_);
v___x_2174_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2173_, v_declName_2108_);
lean_dec_ref(v_env_2173_);
if (lean_obj_tag(v___x_2174_) == 0)
{
v___y_2151_ = v___y_2114_;
v___y_2152_ = v___y_2116_;
goto v___jp_2150_;
}
else
{
lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2189_; 
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; 
v_unused_2190_ = lean_ctor_get(v___x_2174_, 0);
lean_dec(v_unused_2190_);
v___x_2176_ = v___x_2174_;
v_isShared_2177_ = v_isSharedCheck_2189_;
goto v_resetjp_2175_;
}
else
{
lean_dec(v___x_2174_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2189_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
if (v___x_2171_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
lean_dec_ref(v_docs_2109_);
v___x_2178_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2179_ = 1;
v___x_2180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2108_, v___x_2179_);
v___x_2181_ = lean_string_append(v___x_2178_, v___x_2180_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2183_ = lean_string_append(v___x_2181_, v___x_2182_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set_tag(v___x_2176_, 3);
lean_ctor_set(v___x_2176_, 0, v___x_2183_);
v___x_2185_ = v___x_2176_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = l_Lean_MessageData_ofFormat(v___x_2185_);
v___x_2187_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2186_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2187_;
}
}
else
{
lean_del_object(v___x_2176_);
v___y_2151_ = v___y_2114_;
v___y_2152_ = v___y_2116_;
goto v___jp_2150_;
}
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v_docs_2109_);
lean_dec(v_declName_2108_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
v___jp_2118_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_mctx_2134_; lean_object* v_zetaDeltaFVarIds_2135_; lean_object* v_postponed_2136_; lean_object* v_diag_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2148_; 
v___x_2130_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2131_, 0, v___y_2129_);
lean_ctor_set(v___x_2131_, 1, v___y_2128_);
lean_ctor_set(v___x_2131_, 2, v___y_2126_);
lean_ctor_set(v___x_2131_, 3, v___y_2123_);
lean_ctor_set(v___x_2131_, 4, v___y_2125_);
lean_ctor_set(v___x_2131_, 5, v___x_2130_);
lean_ctor_set(v___x_2131_, 6, v___y_2124_);
lean_ctor_set(v___x_2131_, 7, v___y_2120_);
lean_ctor_set(v___x_2131_, 8, v___y_2127_);
lean_ctor_set(v___x_2131_, 9, v___y_2122_);
v___x_2132_ = lean_st_ref_put(v___y_2121_, v___x_2131_);
v___x_2133_ = lean_st_ref_take(v___y_2119_);
v_mctx_2134_ = lean_ctor_get(v___x_2133_, 0);
v_zetaDeltaFVarIds_2135_ = lean_ctor_get(v___x_2133_, 2);
v_postponed_2136_ = lean_ctor_get(v___x_2133_, 3);
v_diag_2137_ = lean_ctor_get(v___x_2133_, 4);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v___x_2133_, 1);
lean_dec(v_unused_2149_);
v___x_2139_ = v___x_2133_;
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_diag_2137_);
lean_inc(v_postponed_2136_);
lean_inc(v_zetaDeltaFVarIds_2135_);
lean_inc(v_mctx_2134_);
lean_dec(v___x_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v___x_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_mctx_2134_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v_zetaDeltaFVarIds_2135_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v_postponed_2136_);
lean_ctor_set(v_reuseFailAlloc_2147_, 4, v_diag_2137_);
v___x_2144_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_st_ref_put(v___y_2119_, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2141_);
return v___x_2146_;
}
}
}
v___jp_2150_:
{
lean_object* v___x_2153_; lean_object* v_env_2154_; lean_object* v_nextMacroScope_2155_; lean_object* v_ngen_2156_; lean_object* v_auxDeclNGen_2157_; lean_object* v_traceState_2158_; lean_object* v_recordedDeps_2159_; lean_object* v_messages_2160_; lean_object* v_infoState_2161_; lean_object* v_snapshotTasks_2162_; lean_object* v___x_2163_; lean_object* v_env_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2153_ = lean_st_ref_take(v___y_2152_);
v_env_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc_ref(v_env_2154_);
v_nextMacroScope_2155_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_nextMacroScope_2155_);
v_ngen_2156_ = lean_ctor_get(v___x_2153_, 2);
lean_inc_ref(v_ngen_2156_);
v_auxDeclNGen_2157_ = lean_ctor_get(v___x_2153_, 3);
lean_inc_ref(v_auxDeclNGen_2157_);
v_traceState_2158_ = lean_ctor_get(v___x_2153_, 4);
lean_inc_ref(v_traceState_2158_);
v_recordedDeps_2159_ = lean_ctor_get(v___x_2153_, 6);
lean_inc_ref(v_recordedDeps_2159_);
v_messages_2160_ = lean_ctor_get(v___x_2153_, 7);
lean_inc_ref(v_messages_2160_);
v_infoState_2161_ = lean_ctor_get(v___x_2153_, 8);
lean_inc_ref(v_infoState_2161_);
v_snapshotTasks_2162_ = lean_ctor_get(v___x_2153_, 9);
lean_inc_ref(v_snapshotTasks_2162_);
lean_dec(v___x_2153_);
v___x_2163_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2108_);
v_env_2164_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2163_, v_env_2154_, v_declName_2108_, v_docs_2109_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_array_get_size(v_deferred_2110_);
v___x_2167_ = lean_nat_dec_lt(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_dec(v_declName_2108_);
v___y_2119_ = v___y_2151_;
v___y_2120_ = v_messages_2160_;
v___y_2121_ = v___y_2152_;
v___y_2122_ = v_snapshotTasks_2162_;
v___y_2123_ = v_auxDeclNGen_2157_;
v___y_2124_ = v_recordedDeps_2159_;
v___y_2125_ = v_traceState_2158_;
v___y_2126_ = v_ngen_2156_;
v___y_2127_ = v_infoState_2161_;
v___y_2128_ = v_nextMacroScope_2155_;
v___y_2129_ = v_env_2164_;
goto v___jp_2118_;
}
else
{
size_t v___x_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = ((size_t)0ULL);
v___x_2169_ = lean_usize_of_nat(v___x_2166_);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2108_, v_deferred_2110_, v___x_2168_, v___x_2169_, v_env_2164_);
v___y_2119_ = v___y_2151_;
v___y_2120_ = v_messages_2160_;
v___y_2121_ = v___y_2152_;
v___y_2122_ = v_snapshotTasks_2162_;
v___y_2123_ = v_auxDeclNGen_2157_;
v___y_2124_ = v_recordedDeps_2159_;
v___y_2125_ = v_traceState_2158_;
v___y_2126_ = v_ngen_2156_;
v___y_2127_ = v_infoState_2161_;
v___y_2128_ = v_nextMacroScope_2155_;
v___y_2129_ = v___x_2170_;
goto v___jp_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2193_, lean_object* v_docs_2194_, lean_object* v_deferred_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2193_, v_docs_2194_, v_deferred_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_deferred_2195_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2204_, lean_object* v_binders_2205_, lean_object* v_docComment_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___x_2234_; lean_object* v_env_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_st_ref_get(v_a_2212_);
v_env_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_env_2235_);
lean_dec(v___x_2234_);
v___x_2236_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2235_, v_declName_2204_);
lean_dec_ref(v_env_2235_);
if (lean_obj_tag(v___x_2236_) == 0)
{
v___y_2215_ = v_a_2207_;
v___y_2216_ = v_a_2208_;
v___y_2217_ = v_a_2209_;
v___y_2218_ = v_a_2210_;
v___y_2219_ = v_a_2211_;
v___y_2220_ = v_a_2212_;
goto v___jp_2214_;
}
else
{
lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_binders_2205_);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2251_ == 0)
{
lean_object* v_unused_2252_; 
v_unused_2252_ = lean_ctor_get(v___x_2236_, 0);
lean_dec(v_unused_2252_);
v___x_2238_ = v___x_2236_;
v_isShared_2239_ = v_isSharedCheck_2251_;
goto v_resetjp_2237_;
}
else
{
lean_dec(v___x_2236_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2251_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2240_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2241_ = 1;
v___x_2242_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2204_, v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2240_, v___x_2242_);
lean_dec_ref(v___x_2242_);
v___x_2244_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2245_ = lean_string_append(v___x_2243_, v___x_2244_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set_tag(v___x_2238_, 3);
lean_ctor_set(v___x_2238_, 0, v___x_2245_);
v___x_2247_ = v___x_2238_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = l_Lean_MessageData_ofFormat(v___x_2247_);
v___x_2249_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2248_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_);
return v___x_2249_;
}
}
}
v___jp_2214_:
{
lean_object* v___x_2221_; 
lean_inc(v_declName_2204_);
v___x_2221_ = l_Lean_versoDocString(v_declName_2204_, v_binders_2205_, v_docComment_2206_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_toVersoDocString_2223_; lean_object* v_deferredChecks_2224_; lean_object* v___x_2225_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v_toVersoDocString_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc_ref(v_toVersoDocString_2223_);
v_deferredChecks_2224_ = lean_ctor_get(v_a_2222_, 1);
lean_inc_ref(v_deferredChecks_2224_);
lean_dec(v_a_2222_);
v___x_2225_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2204_, v_toVersoDocString_2223_, v_deferredChecks_2224_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec_ref(v_deferredChecks_2224_);
return v___x_2225_;
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_declName_2204_);
v_a_2226_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2221_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2221_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2253_, lean_object* v_binders_2254_, lean_object* v_docComment_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_addVersoDocString(v_declName_2253_, v_binders_2254_, v_docComment_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_docComment_2255_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2264_, lean_object* v_msg_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2274_, v_msg_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object* v_msgData_2284_, lean_object* v_macroStack_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2284_, v_macroStack_2285_, v___y_2290_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object* v_msgData_2294_, lean_object* v_macroStack_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2294_, v_macroStack_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2304_, lean_object* v_docComment_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___x_2333_; lean_object* v_env_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_st_ref_get(v_a_2311_);
v_env_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_ref(v_env_2334_);
lean_dec(v___x_2333_);
v___x_2335_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2334_, v_declName_2304_);
lean_dec_ref(v_env_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
v___y_2314_ = v_a_2306_;
v___y_2315_ = v_a_2307_;
v___y_2316_ = v_a_2308_;
v___y_2317_ = v_a_2309_;
v___y_2318_ = v_a_2310_;
v___y_2319_ = v_a_2311_;
goto v___jp_2313_;
}
else
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_docComment_2305_);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2335_, 0);
lean_dec(v_unused_2351_);
v___x_2337_ = v___x_2335_;
v_isShared_2338_ = v_isSharedCheck_2350_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v___x_2335_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2350_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2339_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__0));
v___x_2340_ = 1;
v___x_2341_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2304_, v___x_2340_);
v___x_2342_ = lean_string_append(v___x_2339_, v___x_2341_);
lean_dec_ref(v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__3___closed__1));
v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set_tag(v___x_2337_, 3);
lean_ctor_set(v___x_2337_, 0, v___x_2344_);
v___x_2346_ = v___x_2337_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = l_Lean_MessageData_ofFormat(v___x_2346_);
v___x_2348_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2347_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
return v___x_2348_;
}
}
}
v___jp_2313_:
{
lean_object* v___x_2320_; 
lean_inc(v_declName_2304_);
v___x_2320_ = l_Lean_versoDocStringFromString(v_declName_2304_, v_docComment_2305_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v_toVersoDocString_2322_; lean_object* v_deferredChecks_2323_; lean_object* v___x_2324_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v_toVersoDocString_2322_ = lean_ctor_get(v_a_2321_, 0);
lean_inc_ref(v_toVersoDocString_2322_);
v_deferredChecks_2323_ = lean_ctor_get(v_a_2321_, 1);
lean_inc_ref(v_deferredChecks_2323_);
lean_dec(v_a_2321_);
v___x_2324_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2304_, v_toVersoDocString_2322_, v_deferredChecks_2323_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec_ref(v_deferredChecks_2323_);
return v___x_2324_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_declName_2304_);
v_a_2325_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2320_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2320_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2352_, lean_object* v_docComment_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l_Lean_addVersoDocStringFromString(v_declName_2352_, v_docComment_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_);
lean_dec(v_a_2359_);
lean_dec_ref(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2362_, lean_object* v_msgData_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = 2;
v___x_2370_ = 0;
v___x_2371_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2362_, v_msgData_2363_, v___x_2369_, v___x_2370_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2372_, lean_object* v_msgData_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2372_, v_msgData_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v_ref_2372_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2380_, lean_object* v_str_2381_, lean_object* v_as_2382_, size_t v_sz_2383_, size_t v_i_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_a_2394_; uint8_t v___x_2398_; 
v___x_2398_ = lean_usize_dec_lt(v_i_2384_, v_sz_2383_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_b_2385_);
return v___x_2399_;
}
else
{
lean_object* v_a_2400_; lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v_start_2403_; lean_object* v_stop_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2424_; 
v_a_2400_ = lean_array_uget_borrowed(v_as_2382_, v_i_2384_);
v_fst_2401_ = lean_ctor_get(v_a_2400_, 0);
lean_inc(v_fst_2401_);
v_snd_2402_ = lean_ctor_get(v_a_2400_, 1);
v_start_2403_ = lean_ctor_get(v_fst_2401_, 0);
v_stop_2404_ = lean_ctor_get(v_fst_2401_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_fst_2401_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2406_ = v_fst_2401_;
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_stop_2404_);
lean_inc(v_start_2403_);
lean_dec(v_fst_2401_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2424_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_box(0);
if (lean_obj_tag(v___y_2380_) == 1)
{
lean_object* v_val_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_val_2409_ = lean_ctor_get(v___y_2380_, 0);
v___x_2410_ = lean_nat_add(v_val_2409_, v_start_2403_);
v___x_2411_ = lean_nat_add(v_val_2409_, v_stop_2404_);
v___x_2412_ = 0;
v___x_2413_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2413_, 0, v___x_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*2, v___x_2412_);
v___x_2414_ = lean_string_utf8_extract(v_str_2381_, v_start_2403_, v_stop_2404_);
lean_dec(v_stop_2404_);
lean_dec(v_start_2403_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set_tag(v___x_2406_, 2);
lean_ctor_set(v___x_2406_, 1, v___x_2414_);
lean_ctor_set(v___x_2406_, 0, v___x_2413_);
v___x_2416_ = v___x_2406_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_inc(v_snd_2402_);
v___x_2417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_snd_2402_);
v___x_2418_ = l_Lean_MessageData_ofFormat(v___x_2417_);
v___x_2419_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2416_, v___x_2418_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec_ref(v___x_2416_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_dec_ref_known(v___x_2419_, 1);
v_a_2394_ = v___x_2408_;
goto v___jp_2393_;
}
else
{
return v___x_2419_;
}
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_del_object(v___x_2406_);
lean_dec(v_stop_2404_);
lean_dec(v_start_2403_);
lean_inc(v_snd_2402_);
v___x_2421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_snd_2402_);
v___x_2422_ = l_Lean_MessageData_ofFormat(v___x_2421_);
v___x_2423_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2422_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_dec_ref_known(v___x_2423_, 1);
v_a_2394_ = v___x_2408_;
goto v___jp_2393_;
}
else
{
return v___x_2423_;
}
}
}
}
v___jp_2393_:
{
size_t v___x_2395_; size_t v___x_2396_; 
v___x_2395_ = ((size_t)1ULL);
v___x_2396_ = lean_usize_add(v_i_2384_, v___x_2395_);
v_i_2384_ = v___x_2396_;
v_b_2385_ = v_a_2394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2425_, lean_object* v_str_2426_, lean_object* v_as_2427_, lean_object* v_sz_2428_, lean_object* v_i_2429_, lean_object* v_b_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
size_t v_sz_boxed_2438_; size_t v_i_boxed_2439_; lean_object* v_res_2440_; 
v_sz_boxed_2438_ = lean_unbox_usize(v_sz_2428_);
lean_dec(v_sz_2428_);
v_i_boxed_2439_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_res_2440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2425_, v_str_2426_, v_as_2427_, v_sz_boxed_2438_, v_i_boxed_2439_, v_b_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_as_2427_);
lean_dec_ref(v_str_2426_);
lean_dec(v___y_2425_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_str_2449_; lean_object* v___y_2451_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_str_2449_ = l_Lean_TSyntax_getDocString(v_docstring_2441_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = l_Lean_Syntax_getArg(v_docstring_2441_, v___x_2466_);
v___x_2468_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2467_);
lean_dec(v___x_2467_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_box(0);
v___y_2451_ = v___x_2469_;
goto v___jp_2450_;
}
else
{
lean_object* v_val_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v_val_2470_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2471_ = 0;
v___x_2472_ = l_Lean_SourceInfo_getPos_x3f(v_val_2470_, v___x_2471_);
lean_dec(v_val_2470_);
v___y_2451_ = v___x_2472_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v_fst_2453_; lean_object* v___x_2454_; size_t v_sz_2455_; size_t v___x_2456_; lean_object* v___x_2457_; 
lean_inc_ref(v_str_2449_);
v___x_2452_ = l_Lean_rewriteManualLinksCore(v_str_2449_);
v_fst_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_fst_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = lean_box(0);
v_sz_2455_ = lean_array_size(v_fst_2453_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2451_, v_str_2449_, v_fst_2453_, v_sz_2455_, v___x_2456_, v___x_2454_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v_fst_2453_);
lean_dec_ref(v_str_2449_);
lean_dec(v___y_2451_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2457_, 0);
lean_dec(v_unused_2465_);
v___x_2459_ = v___x_2457_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_dec(v___x_2457_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2454_);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2454_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
return v___x_2457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v_docstring_2473_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2482_, lean_object* v_msg_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_toCold_2491_; lean_object* v_currRecDepth_2492_; lean_object* v_ref_2493_; uint16_t v_optionFlags_2494_; uint8_t v_suppressElabErrors_2495_; uint8_t v_isRecordingDeps_2496_; lean_object* v_ref_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_toCold_2491_ = lean_ctor_get(v___y_2488_, 0);
v_currRecDepth_2492_ = lean_ctor_get(v___y_2488_, 1);
v_ref_2493_ = lean_ctor_get(v___y_2488_, 2);
v_optionFlags_2494_ = lean_ctor_get_uint16(v___y_2488_, sizeof(void*)*3);
v_suppressElabErrors_2495_ = lean_ctor_get_uint8(v___y_2488_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2496_ = lean_ctor_get_uint8(v___y_2488_, sizeof(void*)*3 + 3);
v_ref_2497_ = l_Lean_replaceRef(v_ref_2482_, v_ref_2493_);
lean_inc(v_currRecDepth_2492_);
lean_inc_ref(v_toCold_2491_);
v___x_2498_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2498_, 0, v_toCold_2491_);
lean_ctor_set(v___x_2498_, 1, v_currRecDepth_2492_);
lean_ctor_set(v___x_2498_, 2, v_ref_2497_);
lean_ctor_set_uint16(v___x_2498_, sizeof(void*)*3, v_optionFlags_2494_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 2, v_suppressElabErrors_2495_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*3 + 3, v_isRecordingDeps_2496_);
v___x_2499_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___x_2498_, v___y_2489_);
lean_dec_ref_known(v___x_2498_, 3);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2500_, lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2500_, v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v_ref_2500_);
return v_res_2509_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2512_ = l_Lean_stringToMessageData(v___x_2511_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = l_Lean_Syntax_getArg(v_stx_2514_, v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 1)
{
lean_object* v_kind_2530_; 
v_kind_2530_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_kind_2530_);
if (lean_obj_tag(v_kind_2530_) == 1)
{
lean_object* v_pre_2531_; 
v_pre_2531_ = lean_ctor_get(v_kind_2530_, 0);
lean_inc(v_pre_2531_);
if (lean_obj_tag(v_pre_2531_) == 1)
{
lean_object* v_pre_2532_; 
v_pre_2532_ = lean_ctor_get(v_pre_2531_, 0);
lean_inc(v_pre_2532_);
if (lean_obj_tag(v_pre_2532_) == 1)
{
lean_object* v_pre_2533_; 
v_pre_2533_ = lean_ctor_get(v_pre_2532_, 0);
lean_inc(v_pre_2533_);
if (lean_obj_tag(v_pre_2533_) == 1)
{
lean_object* v_pre_2534_; 
v_pre_2534_ = lean_ctor_get(v_pre_2533_, 0);
if (lean_obj_tag(v_pre_2534_) == 0)
{
lean_object* v_args_2535_; lean_object* v_str_2536_; lean_object* v_str_2537_; lean_object* v_str_2538_; lean_object* v_str_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v_args_2535_ = lean_ctor_get(v___x_2529_, 2);
lean_inc_ref(v_args_2535_);
lean_dec_ref_known(v___x_2529_, 3);
v_str_2536_ = lean_ctor_get(v_kind_2530_, 1);
lean_inc_ref(v_str_2536_);
lean_dec_ref_known(v_kind_2530_, 2);
v_str_2537_ = lean_ctor_get(v_pre_2531_, 1);
lean_inc_ref(v_str_2537_);
lean_dec_ref_known(v_pre_2531_, 2);
v_str_2538_ = lean_ctor_get(v_pre_2532_, 1);
lean_inc_ref(v_str_2538_);
lean_dec_ref_known(v_pre_2532_, 2);
v_str_2539_ = lean_ctor_get(v_pre_2533_, 1);
lean_inc_ref(v_str_2539_);
lean_dec_ref_known(v_pre_2533_, 2);
v___x_2540_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2541_ = lean_string_dec_eq(v_str_2539_, v___x_2540_);
lean_dec_ref(v_str_2539_);
if (v___x_2541_ == 0)
{
lean_dec_ref(v_str_2538_);
lean_dec_ref(v_str_2537_);
lean_dec_ref(v_str_2536_);
lean_dec_ref(v_args_2535_);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2543_ = lean_string_dec_eq(v_str_2538_, v___x_2542_);
lean_dec_ref(v_str_2538_);
if (v___x_2543_ == 0)
{
lean_dec_ref(v_str_2537_);
lean_dec_ref(v_str_2536_);
lean_dec_ref(v_args_2535_);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2544_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2545_ = lean_string_dec_eq(v_str_2537_, v___x_2544_);
lean_dec_ref(v_str_2537_);
if (v___x_2545_ == 0)
{
lean_dec_ref(v_str_2536_);
lean_dec_ref(v_args_2535_);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2546_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2547_ = lean_string_dec_eq(v_str_2536_, v___x_2546_);
lean_dec_ref(v_str_2536_);
if (v___x_2547_ == 0)
{
lean_dec_ref(v_args_2535_);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2548_ = lean_array_get_size(v_args_2535_);
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = lean_nat_dec_eq(v___x_2548_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_dec_ref(v_args_2535_);
goto v___jp_2522_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_fget(v_args_2535_, v___x_2551_);
lean_dec_ref(v_args_2535_);
if (lean_obj_tag(v___x_2552_) == 2)
{
lean_object* v_val_2553_; lean_object* v___x_2554_; 
lean_dec(v_stx_2514_);
v_val_2553_ = lean_ctor_get(v___x_2552_, 1);
lean_inc_ref(v_val_2553_);
lean_dec_ref_known(v___x_2552_, 2);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_val_2553_);
return v___x_2554_;
}
else
{
lean_dec(v___x_2552_);
goto v___jp_2522_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2533_, 2);
lean_dec_ref_known(v_pre_2532_, 2);
lean_dec_ref_known(v_pre_2531_, 2);
lean_dec_ref_known(v_kind_2530_, 2);
lean_dec_ref_known(v___x_2529_, 3);
goto v___jp_2522_;
}
}
else
{
lean_dec_ref_known(v_pre_2532_, 2);
lean_dec(v_pre_2533_);
lean_dec_ref_known(v_pre_2531_, 2);
lean_dec_ref_known(v_kind_2530_, 2);
lean_dec_ref_known(v___x_2529_, 3);
goto v___jp_2522_;
}
}
else
{
lean_dec(v_pre_2532_);
lean_dec_ref_known(v_pre_2531_, 2);
lean_dec_ref_known(v_kind_2530_, 2);
lean_dec_ref_known(v___x_2529_, 3);
goto v___jp_2522_;
}
}
else
{
lean_dec_ref_known(v_kind_2530_, 2);
lean_dec(v_pre_2531_);
lean_dec_ref_known(v___x_2529_, 3);
goto v___jp_2522_;
}
}
else
{
lean_dec(v_kind_2530_);
lean_dec_ref_known(v___x_2529_, 3);
goto v___jp_2522_;
}
}
else
{
lean_dec(v___x_2529_);
goto v___jp_2522_;
}
v___jp_2522_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2523_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2514_);
v___x_2524_ = l_Lean_MessageData_ofSyntax(v_stx_2514_);
v___x_2525_ = l_Lean_indentD(v___x_2524_);
v___x_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2523_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2514_, v___x_2526_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v_stx_2514_);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2564_, lean_object* v_docComment_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Name_isAnonymous(v_declName_2564_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v_env_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_st_ref_get(v___y_2571_);
v_env_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc_ref(v_env_2639_);
lean_dec(v___x_2638_);
v___x_2640_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2639_, v_declName_2564_);
lean_dec_ref(v_env_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
v___y_2574_ = v___y_2566_;
v___y_2575_ = v___y_2567_;
v___y_2576_ = v___y_2568_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
goto v___jp_2573_;
}
else
{
lean_dec_ref_known(v___x_2640_, 1);
if (v___x_2637_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec(v_docComment_2565_);
v___x_2641_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2642_ = l_Lean_MessageData_ofConstName(v_declName_2564_, v___x_2637_);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2641_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2643_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2645_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2646_;
}
else
{
v___y_2574_ = v___y_2566_;
v___y_2575_ = v___y_2567_;
v___y_2576_ = v___y_2568_;
v___y_2577_ = v___y_2569_;
v___y_2578_ = v___y_2570_;
v___y_2579_ = v___y_2571_;
goto v___jp_2573_;
}
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec(v_docComment_2565_);
lean_dec(v_declName_2564_);
v___x_2647_ = lean_box(0);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
v___jp_2573_:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2565_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2580_, 1);
v___x_2581_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2565_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2628_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2628_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2628_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v_env_2587_; lean_object* v_nextMacroScope_2588_; lean_object* v_ngen_2589_; lean_object* v_auxDeclNGen_2590_; lean_object* v_traceState_2591_; lean_object* v_recordedDeps_2592_; lean_object* v_messages_2593_; lean_object* v_infoState_2594_; lean_object* v_snapshotTasks_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2626_; 
v___x_2586_ = lean_st_ref_take(v___y_2579_);
v_env_2587_ = lean_ctor_get(v___x_2586_, 0);
v_nextMacroScope_2588_ = lean_ctor_get(v___x_2586_, 1);
v_ngen_2589_ = lean_ctor_get(v___x_2586_, 2);
v_auxDeclNGen_2590_ = lean_ctor_get(v___x_2586_, 3);
v_traceState_2591_ = lean_ctor_get(v___x_2586_, 4);
v_recordedDeps_2592_ = lean_ctor_get(v___x_2586_, 6);
v_messages_2593_ = lean_ctor_get(v___x_2586_, 7);
v_infoState_2594_ = lean_ctor_get(v___x_2586_, 8);
v_snapshotTasks_2595_ = lean_ctor_get(v___x_2586_, 9);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v___x_2586_, 5);
lean_dec(v_unused_2627_);
v___x_2597_ = v___x_2586_;
v_isShared_2598_ = v_isSharedCheck_2626_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_snapshotTasks_2595_);
lean_inc(v_infoState_2594_);
lean_inc(v_messages_2593_);
lean_inc(v_recordedDeps_2592_);
lean_inc(v_traceState_2591_);
lean_inc(v_auxDeclNGen_2590_);
lean_inc(v_ngen_2589_);
lean_inc(v_nextMacroScope_2588_);
lean_inc(v_env_2587_);
lean_dec(v___x_2586_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2626_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2599_ = l_Lean_docStringExt;
v___x_2600_ = l_String_removeLeadingSpaces(v_a_2582_);
v___x_2601_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2599_, v_env_2587_, v_declName_2564_, v___x_2600_);
v___x_2602_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 5, v___x_2602_);
lean_ctor_set(v___x_2597_, 0, v___x_2601_);
v___x_2604_ = v___x_2597_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_nextMacroScope_2588_);
lean_ctor_set(v_reuseFailAlloc_2625_, 2, v_ngen_2589_);
lean_ctor_set(v_reuseFailAlloc_2625_, 3, v_auxDeclNGen_2590_);
lean_ctor_set(v_reuseFailAlloc_2625_, 4, v_traceState_2591_);
lean_ctor_set(v_reuseFailAlloc_2625_, 5, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2625_, 6, v_recordedDeps_2592_);
lean_ctor_set(v_reuseFailAlloc_2625_, 7, v_messages_2593_);
lean_ctor_set(v_reuseFailAlloc_2625_, 8, v_infoState_2594_);
lean_ctor_set(v_reuseFailAlloc_2625_, 9, v_snapshotTasks_2595_);
v___x_2604_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v_mctx_2607_; lean_object* v_zetaDeltaFVarIds_2608_; lean_object* v_postponed_2609_; lean_object* v_diag_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2623_; 
v___x_2605_ = lean_st_ref_put(v___y_2579_, v___x_2604_);
v___x_2606_ = lean_st_ref_take(v___y_2577_);
v_mctx_2607_ = lean_ctor_get(v___x_2606_, 0);
v_zetaDeltaFVarIds_2608_ = lean_ctor_get(v___x_2606_, 2);
v_postponed_2609_ = lean_ctor_get(v___x_2606_, 3);
v_diag_2610_ = lean_ctor_get(v___x_2606_, 4);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v___x_2606_, 1);
lean_dec(v_unused_2624_);
v___x_2612_ = v___x_2606_;
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_diag_2610_);
lean_inc(v_postponed_2609_);
lean_inc(v_zetaDeltaFVarIds_2608_);
lean_inc(v_mctx_2607_);
lean_dec(v___x_2606_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2623_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 1, v___x_2615_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_mctx_2607_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_zetaDeltaFVarIds_2608_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v_postponed_2609_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v_diag_2610_);
v___x_2617_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2620_; 
v___x_2618_ = lean_st_ref_put(v___y_2577_, v___x_2617_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2614_);
v___x_2620_ = v___x_2584_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2614_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_declName_2564_);
v_a_2629_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2581_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2581_);
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
else
{
lean_dec(v_docComment_2565_);
lean_dec(v_declName_2564_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2649_, lean_object* v_docComment_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2649_, v_docComment_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2659_, lean_object* v_declName_2660_, lean_object* v_binders_2661_, lean_object* v_docComment_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
if (v_isVerso_2659_ == 0)
{
lean_object* v___x_2670_; 
lean_dec(v_binders_2661_);
v___x_2670_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2660_, v_docComment_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_addVersoDocString(v_declName_2660_, v_binders_2661_, v_docComment_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_docComment_2662_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2672_, lean_object* v_declName_2673_, lean_object* v_binders_2674_, lean_object* v_docComment_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
uint8_t v_isVerso_boxed_2683_; lean_object* v_res_2684_; 
v_isVerso_boxed_2683_ = lean_unbox(v_isVerso_2672_);
v_res_2684_ = l_Lean_addDocStringOf(v_isVerso_boxed_2683_, v_declName_2673_, v_binders_2674_, v_docComment_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
lean_dec(v_a_2677_);
lean_dec_ref(v_a_2676_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2685_, lean_object* v_msgData_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2685_, v_msgData_2686_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2695_, lean_object* v_msgData_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2695_, v_msgData_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v_ref_2695_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2705_, lean_object* v_ref_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2706_, v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_ref_2717_, lean_object* v_msg_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2716_, v_ref_2717_, v_msg_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v_ref_2717_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2727_, lean_object* v_t_2728_){
_start:
{
if (lean_obj_tag(v_t_2728_) == 0)
{
lean_object* v_k_2729_; lean_object* v_v_2730_; lean_object* v_l_2731_; lean_object* v_r_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_3386_; 
v_k_2729_ = lean_ctor_get(v_t_2728_, 1);
v_v_2730_ = lean_ctor_get(v_t_2728_, 2);
v_l_2731_ = lean_ctor_get(v_t_2728_, 3);
v_r_2732_ = lean_ctor_get(v_t_2728_, 4);
v_isSharedCheck_3386_ = !lean_is_exclusive(v_t_2728_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v_t_2728_, 0);
lean_dec(v_unused_3387_);
v___x_2734_ = v_t_2728_;
v_isShared_2735_ = v_isSharedCheck_3386_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_r_2732_);
lean_inc(v_l_2731_);
lean_inc(v_v_2730_);
lean_inc(v_k_2729_);
lean_dec(v_t_2728_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_3386_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
uint8_t v___x_2736_; 
v___x_2736_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2727_, v_k_2729_);
switch(v___x_2736_)
{
case 0:
{
lean_object* v_impl_2737_; lean_object* v___x_2738_; 
v_impl_2737_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2727_, v_l_2731_);
v___x_2738_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2737_) == 0)
{
if (lean_obj_tag(v_r_2732_) == 0)
{
lean_object* v_size_2739_; lean_object* v_size_2740_; lean_object* v_k_2741_; lean_object* v_v_2742_; lean_object* v_l_2743_; lean_object* v_r_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v_size_2739_ = lean_ctor_get(v_impl_2737_, 0);
lean_inc(v_size_2739_);
v_size_2740_ = lean_ctor_get(v_r_2732_, 0);
v_k_2741_ = lean_ctor_get(v_r_2732_, 1);
v_v_2742_ = lean_ctor_get(v_r_2732_, 2);
v_l_2743_ = lean_ctor_get(v_r_2732_, 3);
lean_inc(v_l_2743_);
v_r_2744_ = lean_ctor_get(v_r_2732_, 4);
v___x_2745_ = lean_unsigned_to_nat(3u);
v___x_2746_ = lean_nat_mul(v___x_2745_, v_size_2739_);
v___x_2747_ = lean_nat_dec_lt(v___x_2746_, v_size_2740_);
lean_dec(v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
lean_dec(v_l_2743_);
v___x_2748_ = lean_nat_add(v___x_2738_, v_size_2739_);
lean_dec(v_size_2739_);
v___x_2749_ = lean_nat_add(v___x_2748_, v_size_2740_);
lean_dec(v___x_2748_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 3, v_impl_2737_);
lean_ctor_set(v___x_2734_, 0, v___x_2749_);
v___x_2751_ = v___x_2734_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v_impl_2737_);
lean_ctor_set(v_reuseFailAlloc_2752_, 4, v_r_2732_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
else
{
lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2816_; 
lean_inc(v_r_2744_);
lean_inc(v_v_2742_);
lean_inc(v_k_2741_);
lean_inc(v_size_2740_);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; lean_object* v_unused_2818_; lean_object* v_unused_2819_; lean_object* v_unused_2820_; lean_object* v_unused_2821_; 
v_unused_2817_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2817_);
v_unused_2818_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v_r_2732_, 2);
lean_dec(v_unused_2819_);
v_unused_2820_ = lean_ctor_get(v_r_2732_, 1);
lean_dec(v_unused_2820_);
v_unused_2821_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_2821_);
v___x_2754_ = v_r_2732_;
v_isShared_2755_ = v_isSharedCheck_2816_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v_r_2732_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2816_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v_size_2756_; lean_object* v_k_2757_; lean_object* v_v_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v_size_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v_size_2756_ = lean_ctor_get(v_l_2743_, 0);
v_k_2757_ = lean_ctor_get(v_l_2743_, 1);
v_v_2758_ = lean_ctor_get(v_l_2743_, 2);
v_l_2759_ = lean_ctor_get(v_l_2743_, 3);
v_r_2760_ = lean_ctor_get(v_l_2743_, 4);
v_size_2761_ = lean_ctor_get(v_r_2744_, 0);
v___x_2762_ = lean_unsigned_to_nat(2u);
v___x_2763_ = lean_nat_mul(v___x_2762_, v_size_2761_);
v___x_2764_ = lean_nat_dec_lt(v_size_2756_, v___x_2763_);
lean_dec(v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2792_; 
lean_inc(v_r_2760_);
lean_inc(v_l_2759_);
lean_inc(v_v_2758_);
lean_inc(v_k_2757_);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_l_2743_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; lean_object* v_unused_2794_; lean_object* v_unused_2795_; lean_object* v_unused_2796_; lean_object* v_unused_2797_; 
v_unused_2793_ = lean_ctor_get(v_l_2743_, 4);
lean_dec(v_unused_2793_);
v_unused_2794_ = lean_ctor_get(v_l_2743_, 3);
lean_dec(v_unused_2794_);
v_unused_2795_ = lean_ctor_get(v_l_2743_, 2);
lean_dec(v_unused_2795_);
v_unused_2796_ = lean_ctor_get(v_l_2743_, 1);
lean_dec(v_unused_2796_);
v_unused_2797_ = lean_ctor_get(v_l_2743_, 0);
lean_dec(v_unused_2797_);
v___x_2766_ = v_l_2743_;
v_isShared_2767_ = v_isSharedCheck_2792_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v_l_2743_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2792_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2782_; 
v___x_2768_ = lean_nat_add(v___x_2738_, v_size_2739_);
lean_dec(v_size_2739_);
v___x_2769_ = lean_nat_add(v___x_2768_, v_size_2740_);
lean_dec(v_size_2740_);
if (lean_obj_tag(v_l_2759_) == 0)
{
lean_object* v_size_2790_; 
v_size_2790_ = lean_ctor_get(v_l_2759_, 0);
lean_inc(v_size_2790_);
v___y_2782_ = v_size_2790_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_unsigned_to_nat(0u);
v___y_2782_ = v___x_2791_;
goto v___jp_2781_;
}
v___jp_2770_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_nat_add(v___y_2771_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec(v___y_2771_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 4, v_r_2744_);
lean_ctor_set(v___x_2766_, 3, v_r_2760_);
lean_ctor_set(v___x_2766_, 2, v_v_2742_);
lean_ctor_set(v___x_2766_, 1, v_k_2741_);
lean_ctor_set(v___x_2766_, 0, v___x_2774_);
v___x_2776_ = v___x_2766_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_k_2741_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_v_2742_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_r_2760_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_r_2744_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 4, v___x_2776_);
lean_ctor_set(v___x_2754_, 3, v___y_2772_);
lean_ctor_set(v___x_2754_, 2, v_v_2758_);
lean_ctor_set(v___x_2754_, 1, v_k_2757_);
lean_ctor_set(v___x_2754_, 0, v___x_2769_);
v___x_2778_ = v___x_2754_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_k_2757_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_v_2758_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v___y_2772_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
v___jp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_nat_add(v___x_2768_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec(v___x_2768_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_l_2759_);
lean_ctor_set(v___x_2734_, 3, v_impl_2737_);
lean_ctor_set(v___x_2734_, 0, v___x_2783_);
v___x_2785_ = v___x_2734_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2789_, 3, v_impl_2737_);
lean_ctor_set(v_reuseFailAlloc_2789_, 4, v_l_2759_);
v___x_2785_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; 
v___x_2786_ = lean_nat_add(v___x_2738_, v_size_2761_);
if (lean_obj_tag(v_r_2760_) == 0)
{
lean_object* v_size_2787_; 
v_size_2787_ = lean_ctor_get(v_r_2760_, 0);
lean_inc(v_size_2787_);
v___y_2771_ = v___x_2786_;
v___y_2772_ = v___x_2785_;
v___y_2773_ = v_size_2787_;
goto v___jp_2770_;
}
else
{
lean_object* v___x_2788_; 
v___x_2788_ = lean_unsigned_to_nat(0u);
v___y_2771_ = v___x_2786_;
v___y_2772_ = v___x_2785_;
v___y_2773_ = v___x_2788_;
goto v___jp_2770_;
}
}
}
}
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
lean_del_object(v___x_2734_);
v___x_2798_ = lean_nat_add(v___x_2738_, v_size_2739_);
lean_dec(v_size_2739_);
v___x_2799_ = lean_nat_add(v___x_2798_, v_size_2740_);
lean_dec(v_size_2740_);
v___x_2800_ = lean_nat_add(v___x_2798_, v_size_2756_);
lean_dec(v___x_2798_);
lean_inc_ref(v_impl_2737_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 4, v_l_2743_);
lean_ctor_set(v___x_2754_, 3, v_impl_2737_);
lean_ctor_set(v___x_2754_, 2, v_v_2730_);
lean_ctor_set(v___x_2754_, 1, v_k_2729_);
lean_ctor_set(v___x_2754_, 0, v___x_2800_);
v___x_2802_ = v___x_2754_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2800_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_impl_2737_);
lean_ctor_set(v_reuseFailAlloc_2815_, 4, v_l_2743_);
v___x_2802_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_isSharedCheck_2809_ = !lean_is_exclusive(v_impl_2737_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; lean_object* v_unused_2811_; lean_object* v_unused_2812_; lean_object* v_unused_2813_; lean_object* v_unused_2814_; 
v_unused_2810_ = lean_ctor_get(v_impl_2737_, 4);
lean_dec(v_unused_2810_);
v_unused_2811_ = lean_ctor_get(v_impl_2737_, 3);
lean_dec(v_unused_2811_);
v_unused_2812_ = lean_ctor_get(v_impl_2737_, 2);
lean_dec(v_unused_2812_);
v_unused_2813_ = lean_ctor_get(v_impl_2737_, 1);
lean_dec(v_unused_2813_);
v_unused_2814_ = lean_ctor_get(v_impl_2737_, 0);
lean_dec(v_unused_2814_);
v___x_2804_ = v_impl_2737_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_dec(v_impl_2737_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 4, v_r_2744_);
lean_ctor_set(v___x_2804_, 3, v___x_2802_);
lean_ctor_set(v___x_2804_, 2, v_v_2742_);
lean_ctor_set(v___x_2804_, 1, v_k_2741_);
lean_ctor_set(v___x_2804_, 0, v___x_2799_);
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2808_, 1, v_k_2741_);
lean_ctor_set(v_reuseFailAlloc_2808_, 2, v_v_2742_);
lean_ctor_set(v_reuseFailAlloc_2808_, 3, v___x_2802_);
lean_ctor_set(v_reuseFailAlloc_2808_, 4, v_r_2744_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v_size_2822_ = lean_ctor_get(v_impl_2737_, 0);
lean_inc(v_size_2822_);
v___x_2823_ = lean_nat_add(v___x_2738_, v_size_2822_);
lean_dec(v_size_2822_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 3, v_impl_2737_);
lean_ctor_set(v___x_2734_, 0, v___x_2823_);
v___x_2825_ = v___x_2734_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_impl_2737_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v_r_2732_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
if (lean_obj_tag(v_r_2732_) == 0)
{
lean_object* v_l_2827_; 
v_l_2827_ = lean_ctor_get(v_r_2732_, 3);
lean_inc(v_l_2827_);
if (lean_obj_tag(v_l_2827_) == 0)
{
lean_object* v_r_2828_; 
v_r_2828_ = lean_ctor_get(v_r_2732_, 4);
lean_inc(v_r_2828_);
if (lean_obj_tag(v_r_2828_) == 0)
{
lean_object* v_size_2829_; lean_object* v_k_2830_; lean_object* v_v_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2844_; 
v_size_2829_ = lean_ctor_get(v_r_2732_, 0);
v_k_2830_ = lean_ctor_get(v_r_2732_, 1);
v_v_2831_ = lean_ctor_get(v_r_2732_, 2);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; 
v_unused_2845_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2846_);
v___x_2833_ = v_r_2732_;
v_isShared_2834_ = v_isSharedCheck_2844_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_v_2831_);
lean_inc(v_k_2830_);
lean_inc(v_size_2829_);
lean_dec(v_r_2732_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2844_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v_size_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v_size_2835_ = lean_ctor_get(v_l_2827_, 0);
v___x_2836_ = lean_nat_add(v___x_2738_, v_size_2829_);
lean_dec(v_size_2829_);
v___x_2837_ = lean_nat_add(v___x_2738_, v_size_2835_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 4, v_l_2827_);
lean_ctor_set(v___x_2833_, 3, v_impl_2737_);
lean_ctor_set(v___x_2833_, 2, v_v_2730_);
lean_ctor_set(v___x_2833_, 1, v_k_2729_);
lean_ctor_set(v___x_2833_, 0, v___x_2837_);
v___x_2839_ = v___x_2833_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_impl_2737_);
lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_l_2827_);
v___x_2839_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2841_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2828_);
lean_ctor_set(v___x_2734_, 3, v___x_2839_);
lean_ctor_set(v___x_2734_, 2, v_v_2831_);
lean_ctor_set(v___x_2734_, 1, v_k_2830_);
lean_ctor_set(v___x_2734_, 0, v___x_2836_);
v___x_2841_ = v___x_2734_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_k_2830_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_v_2831_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_r_2828_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_object* v_k_2847_; lean_object* v_v_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2871_; 
v_k_2847_ = lean_ctor_get(v_r_2732_, 1);
v_v_2848_ = lean_ctor_get(v_r_2732_, 2);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2871_ == 0)
{
lean_object* v_unused_2872_; lean_object* v_unused_2873_; lean_object* v_unused_2874_; 
v_unused_2872_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2872_);
v_unused_2873_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2873_);
v_unused_2874_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_2874_);
v___x_2850_ = v_r_2732_;
v_isShared_2851_ = v_isSharedCheck_2871_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_v_2848_);
lean_inc(v_k_2847_);
lean_dec(v_r_2732_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2871_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_k_2852_; lean_object* v_v_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2867_; 
v_k_2852_ = lean_ctor_get(v_l_2827_, 1);
v_v_2853_ = lean_ctor_get(v_l_2827_, 2);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_l_2827_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; lean_object* v_unused_2869_; lean_object* v_unused_2870_; 
v_unused_2868_ = lean_ctor_get(v_l_2827_, 4);
lean_dec(v_unused_2868_);
v_unused_2869_ = lean_ctor_get(v_l_2827_, 3);
lean_dec(v_unused_2869_);
v_unused_2870_ = lean_ctor_get(v_l_2827_, 0);
lean_dec(v_unused_2870_);
v___x_2855_ = v_l_2827_;
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_v_2853_);
lean_inc(v_k_2852_);
lean_dec(v_l_2827_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2867_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_unsigned_to_nat(3u);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 4, v_r_2828_);
lean_ctor_set(v___x_2855_, 3, v_r_2828_);
lean_ctor_set(v___x_2855_, 2, v_v_2730_);
lean_ctor_set(v___x_2855_, 1, v_k_2729_);
lean_ctor_set(v___x_2855_, 0, v___x_2738_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2866_, 3, v_r_2828_);
lean_ctor_set(v_reuseFailAlloc_2866_, 4, v_r_2828_);
v___x_2859_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2861_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 3, v_r_2828_);
lean_ctor_set(v___x_2850_, 0, v___x_2738_);
v___x_2861_ = v___x_2850_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_k_2847_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_v_2848_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_r_2828_);
lean_ctor_set(v_reuseFailAlloc_2865_, 4, v_r_2828_);
v___x_2861_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2863_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_2861_);
lean_ctor_set(v___x_2734_, 3, v___x_2859_);
lean_ctor_set(v___x_2734_, 2, v_v_2853_);
lean_ctor_set(v___x_2734_, 1, v_k_2852_);
lean_ctor_set(v___x_2734_, 0, v___x_2857_);
v___x_2863_ = v___x_2734_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_k_2852_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_v_2853_);
lean_ctor_set(v_reuseFailAlloc_2864_, 3, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2864_, 4, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2875_; 
v_r_2875_ = lean_ctor_get(v_r_2732_, 4);
lean_inc(v_r_2875_);
if (lean_obj_tag(v_r_2875_) == 0)
{
lean_object* v_k_2876_; lean_object* v_v_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v_k_2876_ = lean_ctor_get(v_r_2732_, 1);
v_v_2877_ = lean_ctor_get(v_r_2732_, 2);
v_isSharedCheck_2888_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; lean_object* v_unused_2890_; lean_object* v_unused_2891_; 
v_unused_2889_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2889_);
v_unused_2890_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2890_);
v_unused_2891_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_2891_);
v___x_2879_ = v_r_2732_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_v_2877_);
lean_inc(v_k_2876_);
lean_dec(v_r_2732_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(3u);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v_l_2827_);
lean_ctor_set(v___x_2879_, 2, v_v_2730_);
lean_ctor_set(v___x_2879_, 1, v_k_2729_);
lean_ctor_set(v___x_2879_, 0, v___x_2738_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_l_2827_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_l_2827_);
v___x_2883_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_2875_);
lean_ctor_set(v___x_2734_, 3, v___x_2883_);
lean_ctor_set(v___x_2734_, 2, v_v_2877_);
lean_ctor_set(v___x_2734_, 1, v_k_2876_);
lean_ctor_set(v___x_2734_, 0, v___x_2881_);
v___x_2885_ = v___x_2734_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_k_2876_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_v_2877_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_r_2875_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_size_2892_; lean_object* v_k_2893_; lean_object* v_v_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2905_; 
v_size_2892_ = lean_ctor_get(v_r_2732_, 0);
v_k_2893_ = lean_ctor_get(v_r_2732_, 1);
v_v_2894_ = lean_ctor_get(v_r_2732_, 2);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2905_ == 0)
{
lean_object* v_unused_2906_; lean_object* v_unused_2907_; 
v_unused_2906_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2906_);
v_unused_2907_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2907_);
v___x_2896_ = v_r_2732_;
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_v_2894_);
lean_inc(v_k_2893_);
lean_inc(v_size_2892_);
lean_dec(v_r_2732_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 3, v_r_2875_);
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_size_2892_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_k_2893_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_v_2894_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_r_2875_);
lean_ctor_set(v_reuseFailAlloc_2904_, 4, v_r_2875_);
v___x_2899_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = lean_unsigned_to_nat(2u);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_2899_);
lean_ctor_set(v___x_2734_, 3, v_r_2875_);
lean_ctor_set(v___x_2734_, 0, v___x_2900_);
v___x_2902_ = v___x_2734_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_r_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v___x_2899_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
else
{
lean_object* v___x_2909_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 3, v_r_2732_);
lean_ctor_set(v___x_2734_, 0, v___x_2738_);
v___x_2909_ = v___x_2734_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_r_2732_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_r_2732_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2734_);
lean_dec(v_v_2730_);
lean_dec(v_k_2729_);
if (lean_obj_tag(v_l_2731_) == 0)
{
if (lean_obj_tag(v_r_2732_) == 0)
{
lean_object* v_size_2911_; lean_object* v_k_2912_; lean_object* v_v_2913_; lean_object* v_l_2914_; lean_object* v_r_2915_; lean_object* v_size_2916_; lean_object* v_k_2917_; lean_object* v_v_2918_; lean_object* v_l_2919_; lean_object* v_r_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v_size_2911_ = lean_ctor_get(v_l_2731_, 0);
v_k_2912_ = lean_ctor_get(v_l_2731_, 1);
v_v_2913_ = lean_ctor_get(v_l_2731_, 2);
v_l_2914_ = lean_ctor_get(v_l_2731_, 3);
v_r_2915_ = lean_ctor_get(v_l_2731_, 4);
lean_inc(v_r_2915_);
v_size_2916_ = lean_ctor_get(v_r_2732_, 0);
v_k_2917_ = lean_ctor_get(v_r_2732_, 1);
v_v_2918_ = lean_ctor_get(v_r_2732_, 2);
v_l_2919_ = lean_ctor_get(v_r_2732_, 3);
lean_inc(v_l_2919_);
v_r_2920_ = lean_ctor_get(v_r_2732_, 4);
v___x_2921_ = lean_unsigned_to_nat(1u);
v___x_2922_ = lean_nat_dec_lt(v_size_2911_, v_size_2916_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_3058_; 
lean_inc(v_l_2914_);
lean_inc(v_v_2913_);
lean_inc(v_k_2912_);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; lean_object* v_unused_3060_; lean_object* v_unused_3061_; lean_object* v_unused_3062_; lean_object* v_unused_3063_; 
v_unused_3059_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3059_);
v_unused_3060_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3060_);
v_unused_3061_ = lean_ctor_get(v_l_2731_, 2);
lean_dec(v_unused_3061_);
v_unused_3062_ = lean_ctor_get(v_l_2731_, 1);
lean_dec(v_unused_3062_);
v_unused_3063_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3063_);
v___x_2924_ = v_l_2731_;
v_isShared_2925_ = v_isSharedCheck_3058_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v_l_2731_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_3058_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v_tree_2927_; 
v___x_2926_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2912_, v_v_2913_, v_l_2914_, v_r_2915_);
v_tree_2927_ = lean_ctor_get(v___x_2926_, 2);
lean_inc(v_tree_2927_);
if (lean_obj_tag(v_tree_2927_) == 0)
{
lean_object* v_k_2928_; lean_object* v_v_2929_; lean_object* v_size_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v_k_2928_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_k_2928_);
v_v_2929_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_v_2929_);
lean_dec_ref(v___x_2926_);
v_size_2930_ = lean_ctor_get(v_tree_2927_, 0);
v___x_2931_ = lean_unsigned_to_nat(3u);
v___x_2932_ = lean_nat_mul(v___x_2931_, v_size_2930_);
v___x_2933_ = lean_nat_dec_lt(v___x_2932_, v_size_2916_);
lean_dec(v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
lean_dec(v_l_2919_);
v___x_2934_ = lean_nat_add(v___x_2921_, v_size_2930_);
v___x_2935_ = lean_nat_add(v___x_2934_, v_size_2916_);
lean_dec(v___x_2934_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v_r_2732_);
lean_ctor_set(v___x_2924_, 3, v_tree_2927_);
lean_ctor_set(v___x_2924_, 2, v_v_2929_);
lean_ctor_set(v___x_2924_, 1, v_k_2928_);
lean_ctor_set(v___x_2924_, 0, v___x_2935_);
v___x_2937_ = v___x_2924_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_tree_2927_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_r_2732_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
else
{
lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2993_; 
lean_inc(v_r_2920_);
lean_inc(v_v_2918_);
lean_inc(v_k_2917_);
lean_inc(v_size_2916_);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; lean_object* v_unused_2995_; lean_object* v_unused_2996_; lean_object* v_unused_2997_; lean_object* v_unused_2998_; 
v_unused_2994_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_2995_);
v_unused_2996_ = lean_ctor_get(v_r_2732_, 2);
lean_dec(v_unused_2996_);
v_unused_2997_ = lean_ctor_get(v_r_2732_, 1);
lean_dec(v_unused_2997_);
v_unused_2998_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_2998_);
v___x_2940_ = v_r_2732_;
v_isShared_2941_ = v_isSharedCheck_2993_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v_r_2732_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2993_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_size_2942_; lean_object* v_k_2943_; lean_object* v_v_2944_; lean_object* v_l_2945_; lean_object* v_r_2946_; lean_object* v_size_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v_size_2942_ = lean_ctor_get(v_l_2919_, 0);
v_k_2943_ = lean_ctor_get(v_l_2919_, 1);
v_v_2944_ = lean_ctor_get(v_l_2919_, 2);
v_l_2945_ = lean_ctor_get(v_l_2919_, 3);
v_r_2946_ = lean_ctor_get(v_l_2919_, 4);
v_size_2947_ = lean_ctor_get(v_r_2920_, 0);
v___x_2948_ = lean_unsigned_to_nat(2u);
v___x_2949_ = lean_nat_mul(v___x_2948_, v_size_2947_);
v___x_2950_ = lean_nat_dec_lt(v_size_2942_, v___x_2949_);
lean_dec(v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2978_; 
lean_inc(v_r_2946_);
lean_inc(v_l_2945_);
lean_inc(v_v_2944_);
lean_inc(v_k_2943_);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_l_2919_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; lean_object* v_unused_2980_; lean_object* v_unused_2981_; lean_object* v_unused_2982_; lean_object* v_unused_2983_; 
v_unused_2979_ = lean_ctor_get(v_l_2919_, 4);
lean_dec(v_unused_2979_);
v_unused_2980_ = lean_ctor_get(v_l_2919_, 3);
lean_dec(v_unused_2980_);
v_unused_2981_ = lean_ctor_get(v_l_2919_, 2);
lean_dec(v_unused_2981_);
v_unused_2982_ = lean_ctor_get(v_l_2919_, 1);
lean_dec(v_unused_2982_);
v_unused_2983_ = lean_ctor_get(v_l_2919_, 0);
lean_dec(v_unused_2983_);
v___x_2952_ = v_l_2919_;
v_isShared_2953_ = v_isSharedCheck_2978_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_l_2919_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2978_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2968_; 
v___x_2954_ = lean_nat_add(v___x_2921_, v_size_2930_);
v___x_2955_ = lean_nat_add(v___x_2954_, v_size_2916_);
lean_dec(v_size_2916_);
if (lean_obj_tag(v_l_2945_) == 0)
{
lean_object* v_size_2976_; 
v_size_2976_ = lean_ctor_get(v_l_2945_, 0);
lean_inc(v_size_2976_);
v___y_2968_ = v_size_2976_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
v___y_2968_ = v___x_2977_;
goto v___jp_2967_;
}
v___jp_2956_:
{
lean_object* v___x_2960_; lean_object* v___x_2962_; 
v___x_2960_ = lean_nat_add(v___y_2957_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec(v___y_2957_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 4, v_r_2920_);
lean_ctor_set(v___x_2952_, 3, v_r_2946_);
lean_ctor_set(v___x_2952_, 2, v_v_2918_);
lean_ctor_set(v___x_2952_, 1, v_k_2917_);
lean_ctor_set(v___x_2952_, 0, v___x_2960_);
v___x_2962_ = v___x_2952_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2960_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v_r_2946_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v_r_2920_);
v___x_2962_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
lean_object* v___x_2964_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v___x_2962_);
lean_ctor_set(v___x_2940_, 3, v___y_2958_);
lean_ctor_set(v___x_2940_, 2, v_v_2944_);
lean_ctor_set(v___x_2940_, 1, v_k_2943_);
lean_ctor_set(v___x_2940_, 0, v___x_2955_);
v___x_2964_ = v___x_2940_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_k_2943_);
lean_ctor_set(v_reuseFailAlloc_2965_, 2, v_v_2944_);
lean_ctor_set(v_reuseFailAlloc_2965_, 3, v___y_2958_);
lean_ctor_set(v_reuseFailAlloc_2965_, 4, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
v___jp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = lean_nat_add(v___x_2954_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec(v___x_2954_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v_l_2945_);
lean_ctor_set(v___x_2924_, 3, v_tree_2927_);
lean_ctor_set(v___x_2924_, 2, v_v_2929_);
lean_ctor_set(v___x_2924_, 1, v_k_2928_);
lean_ctor_set(v___x_2924_, 0, v___x_2969_);
v___x_2971_ = v___x_2924_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_tree_2927_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_l_2945_);
v___x_2971_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_nat_add(v___x_2921_, v_size_2947_);
if (lean_obj_tag(v_r_2946_) == 0)
{
lean_object* v_size_2973_; 
v_size_2973_ = lean_ctor_get(v_r_2946_, 0);
lean_inc(v_size_2973_);
v___y_2957_ = v___x_2972_;
v___y_2958_ = v___x_2971_;
v___y_2959_ = v_size_2973_;
goto v___jp_2956_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v___y_2957_ = v___x_2972_;
v___y_2958_ = v___x_2971_;
v___y_2959_ = v___x_2974_;
goto v___jp_2956_;
}
}
}
}
}
else
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2984_ = lean_nat_add(v___x_2921_, v_size_2930_);
v___x_2985_ = lean_nat_add(v___x_2984_, v_size_2916_);
lean_dec(v_size_2916_);
v___x_2986_ = lean_nat_add(v___x_2984_, v_size_2942_);
lean_dec(v___x_2984_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 4, v_l_2919_);
lean_ctor_set(v___x_2940_, 3, v_tree_2927_);
lean_ctor_set(v___x_2940_, 2, v_v_2929_);
lean_ctor_set(v___x_2940_, 1, v_k_2928_);
lean_ctor_set(v___x_2940_, 0, v___x_2986_);
v___x_2988_ = v___x_2940_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_k_2928_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_v_2929_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_tree_2927_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_l_2919_);
v___x_2988_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2990_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v_r_2920_);
lean_ctor_set(v___x_2924_, 3, v___x_2988_);
lean_ctor_set(v___x_2924_, 2, v_v_2918_);
lean_ctor_set(v___x_2924_, 1, v_k_2917_);
lean_ctor_set(v___x_2924_, 0, v___x_2985_);
v___x_2990_ = v___x_2924_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_r_2920_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
}
}
else
{
lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3052_; 
lean_inc(v_r_2920_);
lean_inc(v_v_2918_);
lean_inc(v_k_2917_);
lean_inc(v_size_2916_);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; lean_object* v_unused_3054_; lean_object* v_unused_3055_; lean_object* v_unused_3056_; lean_object* v_unused_3057_; 
v_unused_3053_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_3053_);
v_unused_3054_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_3054_);
v_unused_3055_ = lean_ctor_get(v_r_2732_, 2);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_r_2732_, 1);
lean_dec(v_unused_3056_);
v_unused_3057_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_3057_);
v___x_3000_ = v_r_2732_;
v_isShared_3001_ = v_isSharedCheck_3052_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v_r_2732_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3052_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
if (lean_obj_tag(v_l_2919_) == 0)
{
if (lean_obj_tag(v_r_2920_) == 0)
{
lean_object* v_k_3002_; lean_object* v_v_3003_; lean_object* v_size_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v_k_3002_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_k_3002_);
v_v_3003_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_v_3003_);
lean_dec_ref(v___x_2926_);
v_size_3004_ = lean_ctor_get(v_l_2919_, 0);
v___x_3005_ = lean_nat_add(v___x_2921_, v_size_2916_);
lean_dec(v_size_2916_);
v___x_3006_ = lean_nat_add(v___x_2921_, v_size_3004_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 4, v_l_2919_);
lean_ctor_set(v___x_3000_, 3, v_tree_2927_);
lean_ctor_set(v___x_3000_, 2, v_v_3003_);
lean_ctor_set(v___x_3000_, 1, v_k_3002_);
lean_ctor_set(v___x_3000_, 0, v___x_3006_);
v___x_3008_ = v___x_3000_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_3002_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_3003_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_tree_2927_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_l_2919_);
v___x_3008_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v_r_2920_);
lean_ctor_set(v___x_2924_, 3, v___x_3008_);
lean_ctor_set(v___x_2924_, 2, v_v_2918_);
lean_ctor_set(v___x_2924_, 1, v_k_2917_);
lean_ctor_set(v___x_2924_, 0, v___x_3005_);
v___x_3010_ = v___x_2924_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_3011_, 3, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3011_, 4, v_r_2920_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
else
{
lean_object* v_k_3013_; lean_object* v_v_3014_; lean_object* v_k_3015_; lean_object* v_v_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_size_2916_);
v_k_3013_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_k_3013_);
v_v_3014_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_v_3014_);
lean_dec_ref(v___x_2926_);
v_k_3015_ = lean_ctor_get(v_l_2919_, 1);
v_v_3016_ = lean_ctor_get(v_l_2919_, 2);
v_isSharedCheck_3030_ = !lean_is_exclusive(v_l_2919_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; lean_object* v_unused_3032_; lean_object* v_unused_3033_; 
v_unused_3031_ = lean_ctor_get(v_l_2919_, 4);
lean_dec(v_unused_3031_);
v_unused_3032_ = lean_ctor_get(v_l_2919_, 3);
lean_dec(v_unused_3032_);
v_unused_3033_ = lean_ctor_get(v_l_2919_, 0);
lean_dec(v_unused_3033_);
v___x_3018_ = v_l_2919_;
v_isShared_3019_ = v_isSharedCheck_3030_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_v_3016_);
lean_inc(v_k_3015_);
lean_dec(v_l_2919_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3030_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3020_ = lean_unsigned_to_nat(3u);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 4, v_r_2920_);
lean_ctor_set(v___x_3018_, 3, v_r_2920_);
lean_ctor_set(v___x_3018_, 2, v_v_3014_);
lean_ctor_set(v___x_3018_, 1, v_k_3013_);
lean_ctor_set(v___x_3018_, 0, v___x_2921_);
v___x_3022_ = v___x_3018_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_k_3013_);
lean_ctor_set(v_reuseFailAlloc_3029_, 2, v_v_3014_);
lean_ctor_set(v_reuseFailAlloc_3029_, 3, v_r_2920_);
lean_ctor_set(v_reuseFailAlloc_3029_, 4, v_r_2920_);
v___x_3022_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3024_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 3, v_r_2920_);
lean_ctor_set(v___x_3000_, 0, v___x_2921_);
v___x_3024_ = v___x_3000_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_3028_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_3028_, 3, v_r_2920_);
lean_ctor_set(v_reuseFailAlloc_3028_, 4, v_r_2920_);
v___x_3024_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v___x_3024_);
lean_ctor_set(v___x_2924_, 3, v___x_3022_);
lean_ctor_set(v___x_2924_, 2, v_v_3016_);
lean_ctor_set(v___x_2924_, 1, v_k_3015_);
lean_ctor_set(v___x_2924_, 0, v___x_3020_);
v___x_3026_ = v___x_2924_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_k_3015_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_v_3016_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2920_) == 0)
{
lean_object* v_k_3034_; lean_object* v_v_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_dec(v_size_2916_);
v_k_3034_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_k_3034_);
v_v_3035_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_v_3035_);
lean_dec_ref(v___x_2926_);
v___x_3036_ = lean_unsigned_to_nat(3u);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 4, v_l_2919_);
lean_ctor_set(v___x_3000_, 2, v_v_3035_);
lean_ctor_set(v___x_3000_, 1, v_k_3034_);
lean_ctor_set(v___x_3000_, 0, v___x_2921_);
v___x_3038_ = v___x_3000_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_k_3034_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_v_3035_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_l_2919_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_l_2919_);
v___x_3038_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v_r_2920_);
lean_ctor_set(v___x_2924_, 3, v___x_3038_);
lean_ctor_set(v___x_2924_, 2, v_v_2918_);
lean_ctor_set(v___x_2924_, 1, v_k_2917_);
lean_ctor_set(v___x_2924_, 0, v___x_3036_);
v___x_3040_ = v___x_2924_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_3041_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_3041_, 3, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3041_, 4, v_r_2920_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
else
{
lean_object* v_k_3043_; lean_object* v_v_3044_; lean_object* v___x_3046_; 
v_k_3043_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_k_3043_);
v_v_3044_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_v_3044_);
lean_dec_ref(v___x_2926_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 3, v_r_2920_);
v___x_3046_ = v___x_3000_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_size_2916_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_k_2917_);
lean_ctor_set(v_reuseFailAlloc_3051_, 2, v_v_2918_);
lean_ctor_set(v_reuseFailAlloc_3051_, 3, v_r_2920_);
lean_ctor_set(v_reuseFailAlloc_3051_, 4, v_r_2920_);
v___x_3046_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_unsigned_to_nat(2u);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 4, v___x_3046_);
lean_ctor_set(v___x_2924_, 3, v_r_2920_);
lean_ctor_set(v___x_2924_, 2, v_v_3044_);
lean_ctor_set(v___x_2924_, 1, v_k_3043_);
lean_ctor_set(v___x_2924_, 0, v___x_3047_);
v___x_3049_ = v___x_2924_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_k_3043_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_v_3044_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_r_2920_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v___x_3046_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
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
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3216_; 
lean_inc(v_r_2920_);
lean_inc(v_v_2918_);
lean_inc(v_k_2917_);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_r_2732_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; lean_object* v_unused_3220_; lean_object* v_unused_3221_; 
v_unused_3217_ = lean_ctor_get(v_r_2732_, 4);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_r_2732_, 3);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_r_2732_, 2);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_r_2732_, 1);
lean_dec(v_unused_3220_);
v_unused_3221_ = lean_ctor_get(v_r_2732_, 0);
lean_dec(v_unused_3221_);
v___x_3065_ = v_r_2732_;
v_isShared_3066_ = v_isSharedCheck_3216_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v_r_2732_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3216_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v_tree_3068_; 
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2917_, v_v_2918_, v_l_2919_, v_r_2920_);
v_tree_3068_ = lean_ctor_get(v___x_3067_, 2);
lean_inc(v_tree_3068_);
if (lean_obj_tag(v_tree_3068_) == 0)
{
lean_object* v_k_3069_; lean_object* v_v_3070_; lean_object* v_size_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v_k_3069_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_k_3069_);
v_v_3070_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_v_3070_);
lean_dec_ref(v___x_3067_);
v_size_3071_ = lean_ctor_get(v_tree_3068_, 0);
v___x_3072_ = lean_unsigned_to_nat(3u);
v___x_3073_ = lean_nat_mul(v___x_3072_, v_size_3071_);
v___x_3074_ = lean_nat_dec_lt(v___x_3073_, v_size_2911_);
lean_dec(v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_r_2915_);
v___x_3075_ = lean_nat_add(v___x_2921_, v_size_2911_);
v___x_3076_ = lean_nat_add(v___x_3075_, v_size_3071_);
lean_dec(v___x_3075_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_tree_3068_);
lean_ctor_set(v___x_3065_, 3, v_l_2731_);
lean_ctor_set(v___x_3065_, 2, v_v_3070_);
lean_ctor_set(v___x_3065_, 1, v_k_3069_);
lean_ctor_set(v___x_3065_, 0, v___x_3076_);
v___x_3078_ = v___x_3065_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_k_3069_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_v_3070_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_tree_3068_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
else
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3145_; 
lean_inc(v_l_2914_);
lean_inc(v_v_2913_);
lean_inc(v_k_2912_);
lean_inc(v_size_2911_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3146_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_l_2731_, 2);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_l_2731_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3150_);
v___x_3081_ = v_l_2731_;
v_isShared_3082_ = v_isSharedCheck_3145_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v_l_2731_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3145_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v_size_3083_; lean_object* v_size_3084_; lean_object* v_k_3085_; lean_object* v_v_3086_; lean_object* v_l_3087_; lean_object* v_r_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v_size_3083_ = lean_ctor_get(v_l_2914_, 0);
v_size_3084_ = lean_ctor_get(v_r_2915_, 0);
v_k_3085_ = lean_ctor_get(v_r_2915_, 1);
v_v_3086_ = lean_ctor_get(v_r_2915_, 2);
v_l_3087_ = lean_ctor_get(v_r_2915_, 3);
v_r_3088_ = lean_ctor_get(v_r_2915_, 4);
v___x_3089_ = lean_unsigned_to_nat(2u);
v___x_3090_ = lean_nat_mul(v___x_3089_, v_size_3083_);
v___x_3091_ = lean_nat_dec_lt(v_size_3084_, v___x_3090_);
lean_dec(v___x_3090_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3129_; 
lean_inc(v_r_3088_);
lean_inc(v_l_3087_);
lean_inc(v_v_3086_);
lean_inc(v_k_3085_);
lean_del_object(v___x_3081_);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_r_2915_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3130_ = lean_ctor_get(v_r_2915_, 4);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_r_2915_, 3);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_r_2915_, 2);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_r_2915_, 1);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_r_2915_, 0);
lean_dec(v_unused_3134_);
v___x_3093_ = v_r_2915_;
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v_r_2915_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___x_3117_; lean_object* v___y_3119_; 
v___x_3095_ = lean_nat_add(v___x_2921_, v_size_2911_);
lean_dec(v_size_2911_);
v___x_3096_ = lean_nat_add(v___x_3095_, v_size_3071_);
lean_dec(v___x_3095_);
v___x_3117_ = lean_nat_add(v___x_2921_, v_size_3083_);
if (lean_obj_tag(v_l_3087_) == 0)
{
lean_object* v_size_3127_; 
v_size_3127_ = lean_ctor_get(v_l_3087_, 0);
lean_inc(v_size_3127_);
v___y_3119_ = v_size_3127_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_unsigned_to_nat(0u);
v___y_3119_ = v___x_3128_;
goto v___jp_3118_;
}
v___jp_3097_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_nat_add(v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec(v___y_3099_);
lean_inc_ref(v_tree_3068_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 4, v_tree_3068_);
lean_ctor_set(v___x_3093_, 3, v_r_3088_);
lean_ctor_set(v___x_3093_, 2, v_v_3070_);
lean_ctor_set(v___x_3093_, 1, v_k_3069_);
lean_ctor_set(v___x_3093_, 0, v___x_3101_);
v___x_3103_ = v___x_3093_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_k_3069_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_v_3070_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_r_3088_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_tree_3068_);
v___x_3103_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_isSharedCheck_3110_ = !lean_is_exclusive(v_tree_3068_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; lean_object* v_unused_3115_; 
v_unused_3111_ = lean_ctor_get(v_tree_3068_, 4);
lean_dec(v_unused_3111_);
v_unused_3112_ = lean_ctor_get(v_tree_3068_, 3);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_tree_3068_, 2);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_tree_3068_, 1);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_tree_3068_, 0);
lean_dec(v_unused_3115_);
v___x_3105_ = v_tree_3068_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v_tree_3068_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 4, v___x_3103_);
lean_ctor_set(v___x_3105_, 3, v___y_3098_);
lean_ctor_set(v___x_3105_, 2, v_v_3086_);
lean_ctor_set(v___x_3105_, 1, v_k_3085_);
lean_ctor_set(v___x_3105_, 0, v___x_3096_);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_k_3085_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_v_3086_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v___y_3098_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v___x_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
v___jp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_nat_add(v___x_3117_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec(v___x_3117_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_l_3087_);
lean_ctor_set(v___x_3065_, 3, v_l_2914_);
lean_ctor_set(v___x_3065_, 2, v_v_2913_);
lean_ctor_set(v___x_3065_, 1, v_k_2912_);
lean_ctor_set(v___x_3065_, 0, v___x_3120_);
v___x_3122_ = v___x_3065_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3126_, 4, v_l_3087_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_nat_add(v___x_2921_, v_size_3071_);
if (lean_obj_tag(v_r_3088_) == 0)
{
lean_object* v_size_3124_; 
v_size_3124_ = lean_ctor_get(v_r_3088_, 0);
lean_inc(v_size_3124_);
v___y_3098_ = v___x_3122_;
v___y_3099_ = v___x_3123_;
v___y_3100_ = v_size_3124_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_unsigned_to_nat(0u);
v___y_3098_ = v___x_3122_;
v___y_3099_ = v___x_3123_;
v___y_3100_ = v___x_3125_;
goto v___jp_3097_;
}
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3135_ = lean_nat_add(v___x_2921_, v_size_2911_);
lean_dec(v_size_2911_);
v___x_3136_ = lean_nat_add(v___x_3135_, v_size_3071_);
lean_dec(v___x_3135_);
v___x_3137_ = lean_nat_add(v___x_2921_, v_size_3071_);
v___x_3138_ = lean_nat_add(v___x_3137_, v_size_3084_);
lean_dec(v___x_3137_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_tree_3068_);
lean_ctor_set(v___x_3065_, 3, v_r_2915_);
lean_ctor_set(v___x_3065_, 2, v_v_3070_);
lean_ctor_set(v___x_3065_, 1, v_k_3069_);
lean_ctor_set(v___x_3065_, 0, v___x_3138_);
v___x_3140_ = v___x_3065_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_k_3069_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_v_3070_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_r_2915_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_tree_3068_);
v___x_3140_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3142_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 4, v___x_3140_);
lean_ctor_set(v___x_3081_, 0, v___x_3136_);
v___x_3142_ = v___x_3081_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2914_) == 0)
{
lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3174_; 
lean_inc_ref(v_l_2914_);
lean_inc(v_v_2913_);
lean_inc(v_k_2912_);
lean_inc(v_size_2911_);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; lean_object* v_unused_3176_; lean_object* v_unused_3177_; lean_object* v_unused_3178_; lean_object* v_unused_3179_; 
v_unused_3175_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3175_);
v_unused_3176_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3176_);
v_unused_3177_ = lean_ctor_get(v_l_2731_, 2);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_l_2731_, 1);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3179_);
v___x_3152_ = v_l_2731_;
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
else
{
lean_dec(v_l_2731_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3174_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
if (lean_obj_tag(v_r_2915_) == 0)
{
lean_object* v_k_3154_; lean_object* v_v_3155_; lean_object* v_size_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3160_; 
v_k_3154_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_k_3154_);
v_v_3155_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_v_3155_);
lean_dec_ref(v___x_3067_);
v_size_3156_ = lean_ctor_get(v_r_2915_, 0);
v___x_3157_ = lean_nat_add(v___x_2921_, v_size_2911_);
lean_dec(v_size_2911_);
v___x_3158_ = lean_nat_add(v___x_2921_, v_size_3156_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_tree_3068_);
lean_ctor_set(v___x_3065_, 3, v_r_2915_);
lean_ctor_set(v___x_3065_, 2, v_v_3155_);
lean_ctor_set(v___x_3065_, 1, v_k_3154_);
lean_ctor_set(v___x_3065_, 0, v___x_3158_);
v___x_3160_ = v___x_3065_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_k_3154_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_v_3155_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_r_2915_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v_tree_3068_);
v___x_3160_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3162_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 4, v___x_3160_);
lean_ctor_set(v___x_3152_, 0, v___x_3157_);
v___x_3162_ = v___x_3152_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
else
{
lean_object* v_k_3165_; lean_object* v_v_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
lean_dec(v_size_2911_);
v_k_3165_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_k_3165_);
v_v_3166_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_v_3166_);
lean_dec_ref(v___x_3067_);
v___x_3167_ = lean_unsigned_to_nat(3u);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_r_2915_);
lean_ctor_set(v___x_3065_, 3, v_r_2915_);
lean_ctor_set(v___x_3065_, 2, v_v_3166_);
lean_ctor_set(v___x_3065_, 1, v_k_3165_);
lean_ctor_set(v___x_3065_, 0, v___x_2921_);
v___x_3169_ = v___x_3065_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_k_3165_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_v_3166_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_r_2915_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_r_2915_);
v___x_3169_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3171_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 4, v___x_3169_);
lean_ctor_set(v___x_3152_, 0, v___x_3167_);
v___x_3171_ = v___x_3152_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2915_) == 0)
{
lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3204_; 
lean_inc(v_l_2914_);
lean_inc(v_v_2913_);
lean_inc(v_k_2912_);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; lean_object* v_unused_3207_; lean_object* v_unused_3208_; lean_object* v_unused_3209_; 
v_unused_3205_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3206_);
v_unused_3207_ = lean_ctor_get(v_l_2731_, 2);
lean_dec(v_unused_3207_);
v_unused_3208_ = lean_ctor_get(v_l_2731_, 1);
lean_dec(v_unused_3208_);
v_unused_3209_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3209_);
v___x_3181_ = v_l_2731_;
v_isShared_3182_ = v_isSharedCheck_3204_;
goto v_resetjp_3180_;
}
else
{
lean_dec(v_l_2731_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3204_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_k_3183_; lean_object* v_v_3184_; lean_object* v_k_3185_; lean_object* v_v_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3200_; 
v_k_3183_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_k_3183_);
v_v_3184_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_v_3184_);
lean_dec_ref(v___x_3067_);
v_k_3185_ = lean_ctor_get(v_r_2915_, 1);
v_v_3186_ = lean_ctor_get(v_r_2915_, 2);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_r_2915_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; lean_object* v_unused_3202_; lean_object* v_unused_3203_; 
v_unused_3201_ = lean_ctor_get(v_r_2915_, 4);
lean_dec(v_unused_3201_);
v_unused_3202_ = lean_ctor_get(v_r_2915_, 3);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_r_2915_, 0);
lean_dec(v_unused_3203_);
v___x_3188_ = v_r_2915_;
v_isShared_3189_ = v_isSharedCheck_3200_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_v_3186_);
lean_inc(v_k_3185_);
lean_dec(v_r_2915_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3200_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3190_ = lean_unsigned_to_nat(3u);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 4, v_l_2914_);
lean_ctor_set(v___x_3188_, 3, v_l_2914_);
lean_ctor_set(v___x_3188_, 2, v_v_2913_);
lean_ctor_set(v___x_3188_, 1, v_k_2912_);
lean_ctor_set(v___x_3188_, 0, v___x_2921_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_2912_);
lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_2913_);
lean_ctor_set(v_reuseFailAlloc_3199_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3199_, 4, v_l_2914_);
v___x_3192_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3194_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_l_2914_);
lean_ctor_set(v___x_3065_, 3, v_l_2914_);
lean_ctor_set(v___x_3065_, 2, v_v_3184_);
lean_ctor_set(v___x_3065_, 1, v_k_3183_);
lean_ctor_set(v___x_3065_, 0, v___x_2921_);
v___x_3194_ = v___x_3065_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_k_3183_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_v_3184_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_l_2914_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_l_2914_);
v___x_3194_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 4, v___x_3194_);
lean_ctor_set(v___x_3181_, 3, v___x_3192_);
lean_ctor_set(v___x_3181_, 2, v_v_3186_);
lean_ctor_set(v___x_3181_, 1, v_k_3185_);
lean_ctor_set(v___x_3181_, 0, v___x_3190_);
v___x_3196_ = v___x_3181_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_k_3185_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_v_3186_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
}
else
{
lean_object* v_k_3210_; lean_object* v_v_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v_k_3210_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_k_3210_);
v_v_3211_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_v_3211_);
lean_dec_ref(v___x_3067_);
v___x_3212_ = lean_unsigned_to_nat(2u);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 4, v_r_2915_);
lean_ctor_set(v___x_3065_, 3, v_l_2731_);
lean_ctor_set(v___x_3065_, 2, v_v_3211_);
lean_ctor_set(v___x_3065_, 1, v_k_3210_);
lean_ctor_set(v___x_3065_, 0, v___x_3212_);
v___x_3214_ = v___x_3065_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v_k_3210_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_v_3211_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v_r_2915_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
}
else
{
return v_l_2731_;
}
}
else
{
return v_r_2732_;
}
}
default: 
{
lean_object* v_impl_3222_; lean_object* v___x_3223_; 
v_impl_3222_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2727_, v_r_2732_);
v___x_3223_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3222_) == 0)
{
if (lean_obj_tag(v_l_2731_) == 0)
{
lean_object* v_size_3224_; lean_object* v_size_3225_; lean_object* v_k_3226_; lean_object* v_v_3227_; lean_object* v_l_3228_; lean_object* v_r_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v_size_3224_ = lean_ctor_get(v_impl_3222_, 0);
lean_inc(v_size_3224_);
v_size_3225_ = lean_ctor_get(v_l_2731_, 0);
v_k_3226_ = lean_ctor_get(v_l_2731_, 1);
v_v_3227_ = lean_ctor_get(v_l_2731_, 2);
v_l_3228_ = lean_ctor_get(v_l_2731_, 3);
v_r_3229_ = lean_ctor_get(v_l_2731_, 4);
lean_inc(v_r_3229_);
v___x_3230_ = lean_unsigned_to_nat(3u);
v___x_3231_ = lean_nat_mul(v___x_3230_, v_size_3224_);
v___x_3232_ = lean_nat_dec_lt(v___x_3231_, v_size_3225_);
lean_dec(v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_dec(v_r_3229_);
v___x_3233_ = lean_nat_add(v___x_3223_, v_size_3225_);
v___x_3234_ = lean_nat_add(v___x_3233_, v_size_3224_);
lean_dec(v_size_3224_);
lean_dec(v___x_3233_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_impl_3222_);
lean_ctor_set(v___x_2734_, 0, v___x_3234_);
v___x_3236_ = v___x_2734_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3237_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3237_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3237_, 4, v_impl_3222_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
else
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3303_; 
lean_inc(v_l_3228_);
lean_inc(v_v_3227_);
lean_inc(v_k_3226_);
lean_inc(v_size_3225_);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; lean_object* v_unused_3307_; lean_object* v_unused_3308_; 
v_unused_3304_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_2731_, 2);
lean_dec(v_unused_3306_);
v_unused_3307_ = lean_ctor_get(v_l_2731_, 1);
lean_dec(v_unused_3307_);
v_unused_3308_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3308_);
v___x_3239_ = v_l_2731_;
v_isShared_3240_ = v_isSharedCheck_3303_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v_l_2731_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3303_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_size_3241_; lean_object* v_size_3242_; lean_object* v_k_3243_; lean_object* v_v_3244_; lean_object* v_l_3245_; lean_object* v_r_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v_size_3241_ = lean_ctor_get(v_l_3228_, 0);
v_size_3242_ = lean_ctor_get(v_r_3229_, 0);
v_k_3243_ = lean_ctor_get(v_r_3229_, 1);
v_v_3244_ = lean_ctor_get(v_r_3229_, 2);
v_l_3245_ = lean_ctor_get(v_r_3229_, 3);
v_r_3246_ = lean_ctor_get(v_r_3229_, 4);
v___x_3247_ = lean_unsigned_to_nat(2u);
v___x_3248_ = lean_nat_mul(v___x_3247_, v_size_3241_);
v___x_3249_ = lean_nat_dec_lt(v_size_3242_, v___x_3248_);
lean_dec(v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3278_; 
lean_inc(v_r_3246_);
lean_inc(v_l_3245_);
lean_inc(v_v_3244_);
lean_inc(v_k_3243_);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_r_3229_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; lean_object* v_unused_3280_; lean_object* v_unused_3281_; lean_object* v_unused_3282_; lean_object* v_unused_3283_; 
v_unused_3279_ = lean_ctor_get(v_r_3229_, 4);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_r_3229_, 3);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_r_3229_, 2);
lean_dec(v_unused_3281_);
v_unused_3282_ = lean_ctor_get(v_r_3229_, 1);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v_r_3229_, 0);
lean_dec(v_unused_3283_);
v___x_3251_ = v_r_3229_;
v_isShared_3252_ = v_isSharedCheck_3278_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v_r_3229_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3278_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___x_3266_; lean_object* v___y_3268_; 
v___x_3253_ = lean_nat_add(v___x_3223_, v_size_3225_);
lean_dec(v_size_3225_);
v___x_3254_ = lean_nat_add(v___x_3253_, v_size_3224_);
lean_dec(v___x_3253_);
v___x_3266_ = lean_nat_add(v___x_3223_, v_size_3241_);
if (lean_obj_tag(v_l_3245_) == 0)
{
lean_object* v_size_3276_; 
v_size_3276_ = lean_ctor_get(v_l_3245_, 0);
lean_inc(v_size_3276_);
v___y_3268_ = v_size_3276_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_unsigned_to_nat(0u);
v___y_3268_ = v___x_3277_;
goto v___jp_3267_;
}
v___jp_3255_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_nat_add(v___y_3256_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec(v___y_3256_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 4, v_impl_3222_);
lean_ctor_set(v___x_3251_, 3, v_r_3246_);
lean_ctor_set(v___x_3251_, 2, v_v_2730_);
lean_ctor_set(v___x_3251_, 1, v_k_2729_);
lean_ctor_set(v___x_3251_, 0, v___x_3259_);
v___x_3261_ = v___x_3251_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v_r_3246_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v_impl_3222_);
v___x_3261_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 4, v___x_3261_);
lean_ctor_set(v___x_3239_, 3, v___y_3257_);
lean_ctor_set(v___x_3239_, 2, v_v_3244_);
lean_ctor_set(v___x_3239_, 1, v_k_3243_);
lean_ctor_set(v___x_3239_, 0, v___x_3254_);
v___x_3263_ = v___x_3239_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_k_3243_);
lean_ctor_set(v_reuseFailAlloc_3264_, 2, v_v_3244_);
lean_ctor_set(v_reuseFailAlloc_3264_, 3, v___y_3257_);
lean_ctor_set(v_reuseFailAlloc_3264_, 4, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3271_; 
v___x_3269_ = lean_nat_add(v___x_3266_, v___y_3268_);
lean_dec(v___y_3268_);
lean_dec(v___x_3266_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_l_3245_);
lean_ctor_set(v___x_2734_, 3, v_l_3228_);
lean_ctor_set(v___x_2734_, 2, v_v_3227_);
lean_ctor_set(v___x_2734_, 1, v_k_3226_);
lean_ctor_set(v___x_2734_, 0, v___x_3269_);
v___x_3271_ = v___x_2734_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3226_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3227_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_l_3228_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v_l_3245_);
v___x_3271_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_nat_add(v___x_3223_, v_size_3224_);
lean_dec(v_size_3224_);
if (lean_obj_tag(v_r_3246_) == 0)
{
lean_object* v_size_3273_; 
v_size_3273_ = lean_ctor_get(v_r_3246_, 0);
lean_inc(v_size_3273_);
v___y_3256_ = v___x_3272_;
v___y_3257_ = v___x_3271_;
v___y_3258_ = v_size_3273_;
goto v___jp_3255_;
}
else
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_unsigned_to_nat(0u);
v___y_3256_ = v___x_3272_;
v___y_3257_ = v___x_3271_;
v___y_3258_ = v___x_3274_;
goto v___jp_3255_;
}
}
}
}
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
lean_del_object(v___x_2734_);
v___x_3284_ = lean_nat_add(v___x_3223_, v_size_3225_);
lean_dec(v_size_3225_);
v___x_3285_ = lean_nat_add(v___x_3284_, v_size_3224_);
lean_dec(v___x_3284_);
v___x_3286_ = lean_nat_add(v___x_3223_, v_size_3224_);
lean_dec(v_size_3224_);
v___x_3287_ = lean_nat_add(v___x_3286_, v_size_3242_);
lean_dec(v___x_3286_);
lean_inc_ref(v_impl_3222_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 4, v_impl_3222_);
lean_ctor_set(v___x_3239_, 3, v_r_3229_);
lean_ctor_set(v___x_3239_, 2, v_v_2730_);
lean_ctor_set(v___x_3239_, 1, v_k_2729_);
lean_ctor_set(v___x_3239_, 0, v___x_3287_);
v___x_3289_ = v___x_3239_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_r_3229_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_impl_3222_);
v___x_3289_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
v_isSharedCheck_3296_ = !lean_is_exclusive(v_impl_3222_);
if (v_isSharedCheck_3296_ == 0)
{
lean_object* v_unused_3297_; lean_object* v_unused_3298_; lean_object* v_unused_3299_; lean_object* v_unused_3300_; lean_object* v_unused_3301_; 
v_unused_3297_ = lean_ctor_get(v_impl_3222_, 4);
lean_dec(v_unused_3297_);
v_unused_3298_ = lean_ctor_get(v_impl_3222_, 3);
lean_dec(v_unused_3298_);
v_unused_3299_ = lean_ctor_get(v_impl_3222_, 2);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_impl_3222_, 1);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_impl_3222_, 0);
lean_dec(v_unused_3301_);
v___x_3291_ = v_impl_3222_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v_impl_3222_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 4, v___x_3289_);
lean_ctor_set(v___x_3291_, 3, v_l_3228_);
lean_ctor_set(v___x_3291_, 2, v_v_3227_);
lean_ctor_set(v___x_3291_, 1, v_k_3226_);
lean_ctor_set(v___x_3291_, 0, v___x_3285_);
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_k_3226_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_v_3227_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_l_3228_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v___x_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_size_3309_ = lean_ctor_get(v_impl_3222_, 0);
lean_inc(v_size_3309_);
v___x_3310_ = lean_nat_add(v___x_3223_, v_size_3309_);
lean_dec(v_size_3309_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_impl_3222_);
lean_ctor_set(v___x_2734_, 0, v___x_3310_);
v___x_3312_ = v___x_2734_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_impl_3222_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
else
{
if (lean_obj_tag(v_l_2731_) == 0)
{
lean_object* v_l_3314_; 
v_l_3314_ = lean_ctor_get(v_l_2731_, 3);
if (lean_obj_tag(v_l_3314_) == 0)
{
lean_object* v_r_3315_; 
lean_inc_ref(v_l_3314_);
v_r_3315_ = lean_ctor_get(v_l_2731_, 4);
lean_inc(v_r_3315_);
if (lean_obj_tag(v_r_3315_) == 0)
{
lean_object* v_size_3316_; lean_object* v_k_3317_; lean_object* v_v_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3331_; 
v_size_3316_ = lean_ctor_get(v_l_2731_, 0);
v_k_3317_ = lean_ctor_get(v_l_2731_, 1);
v_v_3318_ = lean_ctor_get(v_l_2731_, 2);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3331_ == 0)
{
lean_object* v_unused_3332_; lean_object* v_unused_3333_; 
v_unused_3332_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3332_);
v_unused_3333_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3333_);
v___x_3320_ = v_l_2731_;
v_isShared_3321_ = v_isSharedCheck_3331_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_v_3318_);
lean_inc(v_k_3317_);
lean_inc(v_size_3316_);
lean_dec(v_l_2731_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3331_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_size_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3326_; 
v_size_3322_ = lean_ctor_get(v_r_3315_, 0);
v___x_3323_ = lean_nat_add(v___x_3223_, v_size_3316_);
lean_dec(v_size_3316_);
v___x_3324_ = lean_nat_add(v___x_3223_, v_size_3322_);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 4, v_impl_3222_);
lean_ctor_set(v___x_3320_, 3, v_r_3315_);
lean_ctor_set(v___x_3320_, 2, v_v_2730_);
lean_ctor_set(v___x_3320_, 1, v_k_2729_);
lean_ctor_set(v___x_3320_, 0, v___x_3324_);
v___x_3326_ = v___x_3320_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3324_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v_impl_3222_);
v___x_3326_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
lean_object* v___x_3328_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_3326_);
lean_ctor_set(v___x_2734_, 3, v_l_3314_);
lean_ctor_set(v___x_2734_, 2, v_v_3318_);
lean_ctor_set(v___x_2734_, 1, v_k_3317_);
lean_ctor_set(v___x_2734_, 0, v___x_3323_);
v___x_3328_ = v___x_2734_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3323_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_k_3317_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_v_3318_);
lean_ctor_set(v_reuseFailAlloc_3329_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3329_, 4, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v_k_3334_; lean_object* v_v_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3346_; 
v_k_3334_ = lean_ctor_get(v_l_2731_, 1);
v_v_3335_ = lean_ctor_get(v_l_2731_, 2);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; lean_object* v_unused_3348_; lean_object* v_unused_3349_; 
v_unused_3347_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3347_);
v_unused_3348_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3348_);
v_unused_3349_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3349_);
v___x_3337_ = v_l_2731_;
v_isShared_3338_ = v_isSharedCheck_3346_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_v_3335_);
lean_inc(v_k_3334_);
lean_dec(v_l_2731_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3346_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3339_ = lean_unsigned_to_nat(3u);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 3, v_r_3315_);
lean_ctor_set(v___x_3337_, 2, v_v_2730_);
lean_ctor_set(v___x_3337_, 1, v_k_2729_);
lean_ctor_set(v___x_3337_, 0, v___x_3223_);
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3345_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3345_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3345_, 4, v_r_3315_);
v___x_3341_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_3341_);
lean_ctor_set(v___x_2734_, 3, v_l_3314_);
lean_ctor_set(v___x_2734_, 2, v_v_3335_);
lean_ctor_set(v___x_2734_, 1, v_k_3334_);
lean_ctor_set(v___x_2734_, 0, v___x_3339_);
v___x_3343_ = v___x_2734_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_k_3334_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_v_3335_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
else
{
lean_object* v_r_3350_; 
v_r_3350_ = lean_ctor_get(v_l_2731_, 4);
lean_inc(v_r_3350_);
if (lean_obj_tag(v_r_3350_) == 0)
{
lean_object* v_k_3351_; lean_object* v_v_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3375_; 
lean_inc(v_l_3314_);
v_k_3351_ = lean_ctor_get(v_l_2731_, 1);
v_v_3352_ = lean_ctor_get(v_l_2731_, 2);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_l_2731_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; lean_object* v_unused_3378_; 
v_unused_3376_ = lean_ctor_get(v_l_2731_, 4);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_l_2731_, 3);
lean_dec(v_unused_3377_);
v_unused_3378_ = lean_ctor_get(v_l_2731_, 0);
lean_dec(v_unused_3378_);
v___x_3354_ = v_l_2731_;
v_isShared_3355_ = v_isSharedCheck_3375_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_v_3352_);
lean_inc(v_k_3351_);
lean_dec(v_l_2731_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3375_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_k_3356_; lean_object* v_v_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3371_; 
v_k_3356_ = lean_ctor_get(v_r_3350_, 1);
v_v_3357_ = lean_ctor_get(v_r_3350_, 2);
v_isSharedCheck_3371_ = !lean_is_exclusive(v_r_3350_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; lean_object* v_unused_3373_; lean_object* v_unused_3374_; 
v_unused_3372_ = lean_ctor_get(v_r_3350_, 4);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v_r_3350_, 3);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_r_3350_, 0);
lean_dec(v_unused_3374_);
v___x_3359_ = v_r_3350_;
v_isShared_3360_ = v_isSharedCheck_3371_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_v_3357_);
lean_inc(v_k_3356_);
lean_dec(v_r_3350_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3371_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = lean_unsigned_to_nat(3u);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 4, v_l_3314_);
lean_ctor_set(v___x_3359_, 3, v_l_3314_);
lean_ctor_set(v___x_3359_, 2, v_v_3352_);
lean_ctor_set(v___x_3359_, 1, v_k_3351_);
lean_ctor_set(v___x_3359_, 0, v___x_3223_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3351_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3352_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3314_);
v___x_3363_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 4, v_l_3314_);
lean_ctor_set(v___x_3354_, 2, v_v_2730_);
lean_ctor_set(v___x_3354_, 1, v_k_2729_);
lean_ctor_set(v___x_3354_, 0, v___x_3223_);
v___x_3365_ = v___x_3354_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_l_3314_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v___x_3365_);
lean_ctor_set(v___x_2734_, 3, v___x_3363_);
lean_ctor_set(v___x_2734_, 2, v_v_3357_);
lean_ctor_set(v___x_2734_, 1, v_k_3356_);
lean_ctor_set(v___x_2734_, 0, v___x_3361_);
v___x_3367_ = v___x_2734_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3356_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3357_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3379_ = lean_unsigned_to_nat(2u);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_r_3350_);
lean_ctor_set(v___x_2734_, 0, v___x_3379_);
v___x_3381_ = v___x_2734_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_r_3350_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 4, v_l_2731_);
lean_ctor_set(v___x_2734_, 0, v___x_3223_);
v___x_3384_ = v___x_2734_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_k_2729_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_l_2731_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v_l_2731_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
}
}
}
else
{
return v_t_2728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3388_, lean_object* v_t_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3388_, v_t_3389_);
lean_dec(v_k_3388_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v___x_3393_; 
v___x_3393_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3391_, v_x_3392_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3394_, v_x_3395_);
lean_dec(v_declName_3394_);
return v_res_3396_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___f_3408_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___x_3453_; lean_object* v_env_3454_; lean_object* v___x_3455_; 
lean_inc(v_declName_3400_);
v___f_3408_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3408_, 0, v_declName_3400_);
v___x_3453_ = lean_st_ref_get(v___y_3406_);
v_env_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc_ref(v_env_3454_);
lean_dec(v___x_3453_);
v___x_3455_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3454_, v_declName_3400_);
lean_dec_ref(v_env_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec(v_declName_3400_);
v___y_3410_ = v___y_3404_;
v___y_3411_ = v___y_3406_;
goto v___jp_3409_;
}
else
{
uint8_t v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
lean_dec_ref_known(v___x_3455_, 1);
lean_dec_ref(v___f_3408_);
v___x_3456_ = 0;
v___x_3457_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3458_ = l_Lean_MessageData_ofConstName(v_declName_3400_, v___x_3456_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3461_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3462_;
}
v___jp_3409_:
{
lean_object* v___x_3412_; lean_object* v_env_3413_; lean_object* v_nextMacroScope_3414_; lean_object* v_ngen_3415_; lean_object* v_auxDeclNGen_3416_; lean_object* v_traceState_3417_; lean_object* v_recordedDeps_3418_; lean_object* v_messages_3419_; lean_object* v_infoState_3420_; lean_object* v_snapshotTasks_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3451_; 
v___x_3412_ = lean_st_ref_take(v___y_3411_);
v_env_3413_ = lean_ctor_get(v___x_3412_, 0);
v_nextMacroScope_3414_ = lean_ctor_get(v___x_3412_, 1);
v_ngen_3415_ = lean_ctor_get(v___x_3412_, 2);
v_auxDeclNGen_3416_ = lean_ctor_get(v___x_3412_, 3);
v_traceState_3417_ = lean_ctor_get(v___x_3412_, 4);
v_recordedDeps_3418_ = lean_ctor_get(v___x_3412_, 6);
v_messages_3419_ = lean_ctor_get(v___x_3412_, 7);
v_infoState_3420_ = lean_ctor_get(v___x_3412_, 8);
v_snapshotTasks_3421_ = lean_ctor_get(v___x_3412_, 9);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v___x_3412_, 5);
lean_dec(v_unused_3452_);
v___x_3423_ = v___x_3412_;
v_isShared_3424_ = v_isSharedCheck_3451_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snapshotTasks_3421_);
lean_inc(v_infoState_3420_);
lean_inc(v_messages_3419_);
lean_inc(v_recordedDeps_3418_);
lean_inc(v_traceState_3417_);
lean_inc(v_auxDeclNGen_3416_);
lean_inc(v_ngen_3415_);
lean_inc(v_nextMacroScope_3414_);
lean_inc(v_env_3413_);
lean_dec(v___x_3412_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3451_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3425_ = l_Lean_docStringExt;
v___x_3426_ = lean_box(2);
v___x_3427_ = lean_box(0);
v___x_3428_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_3425_, v_env_3413_, v___f_3408_, v___x_3426_, v___x_3427_);
v___x_3429_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 5, v___x_3429_);
lean_ctor_set(v___x_3423_, 0, v___x_3428_);
v___x_3431_ = v___x_3423_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_nextMacroScope_3414_);
lean_ctor_set(v_reuseFailAlloc_3450_, 2, v_ngen_3415_);
lean_ctor_set(v_reuseFailAlloc_3450_, 3, v_auxDeclNGen_3416_);
lean_ctor_set(v_reuseFailAlloc_3450_, 4, v_traceState_3417_);
lean_ctor_set(v_reuseFailAlloc_3450_, 5, v___x_3429_);
lean_ctor_set(v_reuseFailAlloc_3450_, 6, v_recordedDeps_3418_);
lean_ctor_set(v_reuseFailAlloc_3450_, 7, v_messages_3419_);
lean_ctor_set(v_reuseFailAlloc_3450_, 8, v_infoState_3420_);
lean_ctor_set(v_reuseFailAlloc_3450_, 9, v_snapshotTasks_3421_);
v___x_3431_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v_mctx_3434_; lean_object* v_zetaDeltaFVarIds_3435_; lean_object* v_postponed_3436_; lean_object* v_diag_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3448_; 
v___x_3432_ = lean_st_ref_put(v___y_3411_, v___x_3431_);
v___x_3433_ = lean_st_ref_take(v___y_3410_);
v_mctx_3434_ = lean_ctor_get(v___x_3433_, 0);
v_zetaDeltaFVarIds_3435_ = lean_ctor_get(v___x_3433_, 2);
v_postponed_3436_ = lean_ctor_get(v___x_3433_, 3);
v_diag_3437_ = lean_ctor_get(v___x_3433_, 4);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; 
v_unused_3449_ = lean_ctor_get(v___x_3433_, 1);
lean_dec(v_unused_3449_);
v___x_3439_ = v___x_3433_;
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_diag_3437_);
lean_inc(v_postponed_3436_);
lean_inc(v_zetaDeltaFVarIds_3435_);
lean_inc(v_mctx_3434_);
lean_dec(v___x_3433_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 1, v___x_3442_);
v___x_3444_ = v___x_3439_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_mctx_3434_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v___x_3442_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_zetaDeltaFVarIds_3435_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_postponed_3436_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_diag_3437_);
v___x_3444_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_st_ref_put(v___y_3410_, v___x_3444_);
v___x_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3441_);
return v___x_3446_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
return v_res_3471_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3474_ = l_Lean_stringToMessageData(v___x_3473_);
return v___x_3474_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3477_ = l_Lean_stringToMessageData(v___x_3476_);
return v___x_3477_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3480_ = l_Lean_stringToMessageData(v___x_3479_);
return v___x_3480_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3482_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3483_ = l_Lean_stringToMessageData(v___x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; lean_object* v_env_3493_; lean_object* v_ref_3494_; uint8_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3492_ = lean_st_ref_get(v_a_3490_);
v_env_3493_ = lean_ctor_get(v___x_3492_, 0);
lean_inc_ref(v_env_3493_);
lean_dec(v___x_3492_);
v_ref_3494_ = lean_ctor_get(v_a_3489_, 2);
v___x_3495_ = 1;
lean_inc(v_declName_3484_);
v___x_3496_ = l_Lean_findInternalDocString_x3f(v_env_3493_, v_declName_3484_, v___x_3495_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
if (lean_obj_tag(v_a_3497_) == 1)
{
lean_object* v_val_3498_; 
v_val_3498_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3497_, 1);
if (lean_obj_tag(v_val_3498_) == 0)
{
lean_object* v_val_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3520_; 
v_val_3499_ = lean_ctor_get(v_val_3498_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v_val_3498_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3501_ = v_val_3498_;
v_isShared_3502_ = v_isSharedCheck_3520_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_val_3499_);
lean_dec(v_val_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3520_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_removeBuiltinDocString(v_declName_3484_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; 
lean_dec_ref_known(v___x_3503_, 1);
lean_del_object(v___x_3501_);
lean_inc(v_declName_3484_);
v___x_3504_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v___x_3505_; 
lean_dec_ref_known(v___x_3504_, 1);
v___x_3505_ = l_Lean_addVersoDocStringFromString(v_declName_3484_, v_val_3499_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3505_;
}
else
{
lean_dec(v_val_3499_);
lean_dec(v_declName_3484_);
return v___x_3504_;
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3519_; 
lean_dec(v_val_3499_);
lean_dec(v_declName_3484_);
v_a_3506_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3508_ = v___x_3503_;
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3503_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_io_error_to_string(v_a_3506_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set_tag(v___x_3501_, 3);
lean_ctor_set(v___x_3501_, 0, v___x_3510_);
v___x_3512_ = v___x_3501_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3513_ = l_Lean_MessageData_ofFormat(v___x_3512_);
lean_inc(v_ref_3494_);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v_ref_3494_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3514_);
v___x_3516_ = v___x_3508_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
else
{
lean_object* v___x_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec(v_val_3498_);
v___x_3521_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3522_ = 0;
v___x_3523_ = l_Lean_MessageData_ofConstName(v_declName_3484_, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3521_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3526_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3527_;
}
}
else
{
lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v_a_3497_);
v___x_3528_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_MessageData_ofConstName(v_declName_3484_, v___x_3529_);
v___x_3531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3531_, 0, v___x_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3531_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3533_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
return v___x_3534_;
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_declName_3484_);
v_a_3535_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3537_ = v___x_3496_;
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3496_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3539_ = lean_io_error_to_string(v_a_3535_);
v___x_3540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
v___x_3541_ = l_Lean_MessageData_ofFormat(v___x_3540_);
lean_inc(v_ref_3494_);
v___x_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3542_, 0, v_ref_3494_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3542_);
v___x_3544_ = v___x_3537_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l_Lean_makeDocStringVerso(v_declName_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3556_, lean_object* v_k_3557_, lean_object* v_t_3558_, lean_object* v_h_3559_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3557_, v_t_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3561_, lean_object* v_k_3562_, lean_object* v_t_3563_, lean_object* v_h_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3561_, v_k_3562_, v_t_3563_, v_h_3564_);
lean_dec(v_k_3562_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3566_, lean_object* v_binders_3567_, lean_object* v_docComment_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
uint8_t v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = l_Lean_isVersoDocComment(v_docComment_3568_);
v___x_3577_ = l_Lean_addDocStringOf(v___x_3576_, v_declName_3566_, v_binders_3567_, v_docComment_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3578_, lean_object* v_binders_3579_, lean_object* v_docComment_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_addDocString(v_declName_3578_, v_binders_3579_, v_docComment_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3589_, lean_object* v_binders_3590_, lean_object* v_docString_x3f_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3591_) == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec(v_binders_3590_);
lean_dec(v_declName_3589_);
v___x_3599_ = lean_box(0);
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
else
{
lean_object* v_val_3601_; lean_object* v___x_3602_; 
v_val_3601_ = lean_ctor_get(v_docString_x3f_3591_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v_docString_x3f_3591_, 1);
v___x_3602_ = l_Lean_addDocString(v_declName_3589_, v_binders_3590_, v_val_3601_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3603_, lean_object* v_binders_3604_, lean_object* v_docString_x3f_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_addDocString_x27(v_declName_3603_, v_binders_3604_, v_docString_x3f_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v_nextMacroScope_3619_; lean_object* v_ngen_3620_; lean_object* v_auxDeclNGen_3621_; lean_object* v_traceState_3622_; lean_object* v_recordedDeps_3623_; lean_object* v_messages_3624_; lean_object* v_infoState_3625_; lean_object* v_snapshotTasks_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3652_; 
v___x_3618_ = lean_st_ref_take(v___y_3616_);
v_nextMacroScope_3619_ = lean_ctor_get(v___x_3618_, 1);
v_ngen_3620_ = lean_ctor_get(v___x_3618_, 2);
v_auxDeclNGen_3621_ = lean_ctor_get(v___x_3618_, 3);
v_traceState_3622_ = lean_ctor_get(v___x_3618_, 4);
v_recordedDeps_3623_ = lean_ctor_get(v___x_3618_, 6);
v_messages_3624_ = lean_ctor_get(v___x_3618_, 7);
v_infoState_3625_ = lean_ctor_get(v___x_3618_, 8);
v_snapshotTasks_3626_ = lean_ctor_get(v___x_3618_, 9);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; lean_object* v_unused_3654_; 
v_unused_3653_ = lean_ctor_get(v___x_3618_, 5);
lean_dec(v_unused_3653_);
v_unused_3654_ = lean_ctor_get(v___x_3618_, 0);
lean_dec(v_unused_3654_);
v___x_3628_ = v___x_3618_;
v_isShared_3629_ = v_isSharedCheck_3652_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_snapshotTasks_3626_);
lean_inc(v_infoState_3625_);
lean_inc(v_messages_3624_);
lean_inc(v_recordedDeps_3623_);
lean_inc(v_traceState_3622_);
lean_inc(v_auxDeclNGen_3621_);
lean_inc(v_ngen_3620_);
lean_inc(v_nextMacroScope_3619_);
lean_dec(v___x_3618_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3652_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3630_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 5, v___x_3630_);
lean_ctor_set(v___x_3628_, 0, v_env_3614_);
v___x_3632_ = v___x_3628_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_env_3614_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_nextMacroScope_3619_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_ngen_3620_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_auxDeclNGen_3621_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_traceState_3622_);
lean_ctor_set(v_reuseFailAlloc_3651_, 5, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3651_, 6, v_recordedDeps_3623_);
lean_ctor_set(v_reuseFailAlloc_3651_, 7, v_messages_3624_);
lean_ctor_set(v_reuseFailAlloc_3651_, 8, v_infoState_3625_);
lean_ctor_set(v_reuseFailAlloc_3651_, 9, v_snapshotTasks_3626_);
v___x_3632_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v_mctx_3635_; lean_object* v_zetaDeltaFVarIds_3636_; lean_object* v_postponed_3637_; lean_object* v_diag_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3649_; 
v___x_3633_ = lean_st_ref_put(v___y_3616_, v___x_3632_);
v___x_3634_ = lean_st_ref_take(v___y_3615_);
v_mctx_3635_ = lean_ctor_get(v___x_3634_, 0);
v_zetaDeltaFVarIds_3636_ = lean_ctor_get(v___x_3634_, 2);
v_postponed_3637_ = lean_ctor_get(v___x_3634_, 3);
v_diag_3638_ = lean_ctor_get(v___x_3634_, 4);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3649_ == 0)
{
lean_object* v_unused_3650_; 
v_unused_3650_ = lean_ctor_get(v___x_3634_, 1);
lean_dec(v_unused_3650_);
v___x_3640_ = v___x_3634_;
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_diag_3638_);
lean_inc(v_postponed_3637_);
lean_inc(v_zetaDeltaFVarIds_3636_);
lean_inc(v_mctx_3635_);
lean_dec(v___x_3634_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3649_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3642_ = lean_box(0);
v___x_3643_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v___x_3643_);
v___x_3645_ = v___x_3640_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_mctx_3635_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_zetaDeltaFVarIds_3636_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_postponed_3637_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_diag_3638_);
v___x_3645_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_st_ref_put(v___y_3615_, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3642_);
return v___x_3647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3660_, lean_object* v_as_3661_, size_t v_i_3662_, size_t v_stop_3663_, lean_object* v_b_3664_){
_start:
{
uint8_t v___x_3665_; 
v___x_3665_ = lean_usize_dec_eq(v_i_3662_, v_stop_3663_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v_index_3667_; lean_object* v_sourceString_3668_; lean_object* v_imports_3669_; lean_object* v_currNamespace_3670_; lean_object* v_openDecls_3671_; lean_object* v_options_3672_; lean_object* v_check_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3689_; 
v___x_3666_ = lean_array_uget(v_as_3661_, v_i_3662_);
v_index_3667_ = lean_ctor_get(v___x_3666_, 1);
v_sourceString_3668_ = lean_ctor_get(v___x_3666_, 2);
v_imports_3669_ = lean_ctor_get(v___x_3666_, 3);
v_currNamespace_3670_ = lean_ctor_get(v___x_3666_, 4);
v_openDecls_3671_ = lean_ctor_get(v___x_3666_, 5);
v_options_3672_ = lean_ctor_get(v___x_3666_, 6);
v_check_3673_ = lean_ctor_get(v___x_3666_, 7);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3666_, 0);
lean_dec(v_unused_3690_);
v___x_3675_ = v___x_3666_;
v_isShared_3676_ = v_isSharedCheck_3689_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_check_3673_);
lean_inc(v_options_3672_);
lean_inc(v_openDecls_3671_);
lean_inc(v_currNamespace_3670_);
lean_inc(v_imports_3669_);
lean_inc(v_sourceString_3668_);
lean_inc(v_index_3667_);
lean_dec(v___x_3666_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3689_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v_toEnvExtension_3678_; lean_object* v_asyncMode_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3677_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3678_ = lean_ctor_get(v___x_3677_, 0);
v_asyncMode_3679_ = lean_ctor_get(v_toEnvExtension_3678_, 2);
lean_inc(v_n_3660_);
v___x_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3680_, 0, v_n_3660_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3680_);
v___x_3682_ = v___x_3675_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_index_3667_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_sourceString_3668_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_imports_3669_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_currNamespace_3670_);
lean_ctor_set(v_reuseFailAlloc_3688_, 5, v_openDecls_3671_);
lean_ctor_set(v_reuseFailAlloc_3688_, 6, v_options_3672_);
lean_ctor_set(v_reuseFailAlloc_3688_, 7, v_check_3673_);
v___x_3682_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; 
v___x_3683_ = lean_box(0);
v___x_3684_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3677_, v_b_3664_, v___x_3682_, v_asyncMode_3679_, v___x_3683_);
v___x_3685_ = ((size_t)1ULL);
v___x_3686_ = lean_usize_add(v_i_3662_, v___x_3685_);
v_i_3662_ = v___x_3686_;
v_b_3664_ = v___x_3684_;
goto _start;
}
}
}
else
{
lean_dec(v_n_3660_);
return v_b_3664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3691_, lean_object* v_as_3692_, lean_object* v_i_3693_, lean_object* v_stop_3694_, lean_object* v_b_3695_){
_start:
{
size_t v_i_boxed_3696_; size_t v_stop_boxed_3697_; lean_object* v_res_3698_; 
v_i_boxed_3696_ = lean_unbox_usize(v_i_3693_);
lean_dec(v_i_3693_);
v_stop_boxed_3697_ = lean_unbox_usize(v_stop_3694_);
lean_dec(v_stop_3694_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3691_, v_as_3692_, v_i_boxed_3696_, v_stop_boxed_3697_, v_b_3695_);
lean_dec_ref(v_as_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3699_, lean_object* v_deferred_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v_env_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3708_ = lean_st_ref_get(v___y_3706_);
v_env_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc_ref(v_env_3709_);
lean_dec(v___x_3708_);
v___x_3710_ = l_Lean_getMainModuleDoc(v_env_3709_);
v___x_3711_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3710_);
lean_dec_ref(v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
lean_dec_ref(v_docs_3699_);
v___x_3712_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3713_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3712_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3713_;
}
else
{
lean_object* v___x_3714_; lean_object* v_env_3715_; lean_object* v___x_3716_; lean_object* v_size_3717_; lean_object* v___x_3718_; lean_object* v_env_3719_; lean_object* v___x_3720_; 
v___x_3714_ = lean_st_ref_get(v___y_3706_);
v_env_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc_ref(v_env_3715_);
lean_dec(v___x_3714_);
v___x_3716_ = l_Lean_getMainVersoModuleDocs(v_env_3715_);
v_size_3717_ = lean_ctor_get(v___x_3716_, 2);
lean_inc(v_size_3717_);
lean_dec_ref(v___x_3716_);
v___x_3718_ = lean_st_ref_get(v___y_3706_);
v_env_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc_ref(v_env_3719_);
lean_dec(v___x_3718_);
v___x_3720_ = l_Lean_addVersoModuleDocSnippet(v_env_3719_, v_docs_3699_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v_a_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec(v_size_3717_);
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__1___closed__1);
v___x_3723_ = l_Lean_stringToMessageData(v_a_3721_);
v___x_3724_ = l_Lean_indentD(v___x_3723_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3722_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3725_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3726_;
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v_a_3727_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3728_ = lean_unsigned_to_nat(0u);
v___x_3729_ = lean_array_get_size(v_deferred_3700_);
v___x_3730_ = lean_nat_dec_lt(v___x_3728_, v___x_3729_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; 
lean_dec(v_size_3717_);
v___x_3731_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3727_, v___y_3704_, v___y_3706_);
return v___x_3731_;
}
else
{
size_t v___x_3732_; size_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = lean_usize_of_nat(v___x_3729_);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3717_, v_deferred_3700_, v___x_3732_, v___x_3733_, v_a_3727_);
v___x_3735_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3734_, v___y_3704_, v___y_3706_);
return v___x_3735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3736_, lean_object* v_deferred_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3736_, v_deferred_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec_ref(v_deferred_3737_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3746_, lean_object* v_doc_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = l_Lean_versoModDocString(v_range_3746_, v_doc_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v_fst_3757_; lean_object* v_snd_3758_; lean_object* v___x_3759_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v_fst_3757_ = lean_ctor_get(v_a_3756_, 0);
lean_inc(v_fst_3757_);
v_snd_3758_ = lean_ctor_get(v_a_3756_, 1);
lean_inc(v_snd_3758_);
lean_dec(v_a_3756_);
v___x_3759_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3757_, v_snd_3758_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_snd_3758_);
return v___x_3759_;
}
else
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v_a_3760_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3762_ = v___x_3755_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3755_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3760_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3768_, lean_object* v_doc_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_addVersoModDocString(v_range_3768_, v_doc_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_doc_3769_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3778_, v___y_3782_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
return v_res_3795_;
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
