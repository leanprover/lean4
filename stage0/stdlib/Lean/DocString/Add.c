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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Doc_deferredCheckExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_elabModSnippet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_DocM_execForModule___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMainVersoModuleDocs(lean_object*);
lean_object* l_Lean_VersoModuleDocs_terminalNesting(lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_getMainModuleDoc(lean_object*);
uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_addVersoModuleDocSnippet(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_versoDocStringExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadEIO___aux__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Doc_parseFailureKind;
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
uint8_t l_Lean_isVersoDocComment(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_docStringRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "This documentation comment has an unexpected structure, so it cannot be parsed."};
static const lean_object* l_Lean_docStringRange___closed__0 = (const lean_object*)&l_Lean_docStringRange___closed__0_value;
static lean_once_cell_t l_Lean_docStringRange___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_docStringRange___closed__1;
static lean_once_cell_t l_Lean_docStringRange___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_docStringRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_docStringRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_docStringRange___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "invalid doc string, declaration '"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0_value;
static const lean_string_object l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' is in an imported module"};
static const lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Error adding module docs: "};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "Can't add Verso-format module docs because there is already Markdown-format content present."};
static const lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4;
static lean_once_cell_t l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___impl(lean_object* v_x_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_tag_nat(v_x_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorIdx___impl___boxed(lean_object* v_x_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_VersoDocstringMarkup_ctorIdx___impl(v_x_167_);
lean_dec_ref(v_x_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___redArg(lean_object* v_t_169_, lean_object* v_k_170_){
_start:
{
lean_object* v_doc_171_; lean_object* v___x_172_; 
v_doc_171_ = lean_ctor_get(v_t_169_, 0);
lean_inc(v_doc_171_);
lean_dec_ref(v_t_169_);
v___x_172_ = lean_apply_1(v_k_170_, v_doc_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim(lean_object* v_motive_173_, lean_object* v_ctorIdx_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_k_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_175_, v_k_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_ctorElim___boxed(lean_object* v_motive_179_, lean_object* v_ctorIdx_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_k_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_VersoDocstringMarkup_ctorElim(v_motive_179_, v_ctorIdx_180_, v_t_181_, v_h_182_, v_k_183_);
lean_dec(v_ctorIdx_180_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim___redArg(lean_object* v_t_185_, lean_object* v_document_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_185_, v_document_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_document_elim(lean_object* v_motive_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_document_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_189_, v_document_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim___redArg(lean_object* v_t_193_, lean_object* v_parseFailure_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_193_, v_parseFailure_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_parseFailure_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_parseFailure_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_VersoDocstringMarkup_ctorElim___redArg(v_t_197_, v_parseFailure_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx(lean_object* v_x_201_){
_start:
{
lean_object* v_doc_202_; 
v_doc_202_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_doc_202_);
return v_doc_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringMarkup_stx___boxed(lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_VersoDocstringMarkup_stx(v_x_203_);
lean_dec_ref(v_x_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of(lean_object* v_docComment_205_){
_start:
{
lean_object* v___x_206_; lean_object* v_body_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___y_211_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v_body_207_ = l_Lean_Syntax_getArg(v_docComment_205_, v___x_206_);
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = l_Lean_Syntax_getArg(v_docComment_205_, v___x_208_);
v___x_214_ = l_Lean_Syntax_getArg(v_body_207_, v___x_208_);
v___x_215_ = l_Lean_Doc_parseFailureKind;
lean_inc(v___x_214_);
v___x_216_ = l_Lean_Syntax_isOfKind(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_214_);
v___y_211_ = v___x_217_;
goto v___jp_210_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = l_Lean_Syntax_getArg(v___x_214_, v___x_208_);
lean_dec(v___x_214_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___y_211_ = v___x_219_;
goto v___jp_210_;
}
v___jp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = l_Lean_Syntax_getArg(v_body_207_, v___x_206_);
lean_dec(v_body_207_);
v___x_213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_213_, 0, v___x_209_);
lean_ctor_set(v___x_213_, 1, v___y_211_);
lean_ctor_set(v___x_213_, 2, v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_VersoDocstringView_of___boxed(lean_object* v_docComment_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_VersoDocstringView_of(v_docComment_220_);
lean_dec(v_docComment_220_);
return v_res_221_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__0));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__2));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_noSourceLocation(lean_object* v_what_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_229_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__1);
v___x_230_ = l_Lean_stringToMessageData(v_what_228_);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3, &l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3_once, _init_l___private_Lean_DocString_Add_0__Lean_noSourceLocation___closed__3);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__0));
v___x_236_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__1);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__3));
v___x_241_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__4);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__6));
v___x_246_ = l___private_Lean_DocString_Add_0__Lean_noSourceLocation(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__7);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange(lean_object* v_view_249_){
_start:
{
lean_object* v_opener_250_; lean_object* v_markup_251_; lean_object* v_closer_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v_opener_250_ = lean_ctor_get(v_view_249_, 0);
v_markup_251_ = lean_ctor_get(v_view_249_, 1);
v_closer_252_ = lean_ctor_get(v_view_249_, 2);
v___x_253_ = 1;
v___x_254_ = l_Lean_Syntax_getPos_x3f(v_opener_250_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 1)
{
lean_object* v_val_255_; lean_object* v___y_257_; lean_object* v_doc_273_; 
v_val_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_val_255_);
lean_dec_ref_known(v___x_254_, 1);
v_doc_273_ = lean_ctor_get(v_markup_251_, 0);
v___y_257_ = v_doc_273_;
goto v___jp_256_;
v___jp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Syntax_getPos_x3f(v___y_257_, v___x_253_);
if (lean_obj_tag(v___x_258_) == 1)
{
lean_object* v_val_259_; lean_object* v___x_260_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_258_, 1);
v___x_260_ = l_Lean_Syntax_getPos_x3f(v_closer_252_, v___x_253_);
if (lean_obj_tag(v___x_260_) == 1)
{
lean_object* v_val_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_270_; 
v_val_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_270_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_val_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_270_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_val_259_);
lean_ctor_set(v___x_265_, 1, v_val_261_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_val_255_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v___x_271_; 
lean_dec(v___x_260_);
lean_dec(v_val_259_);
lean_dec(v_val_255_);
v___x_271_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_271_;
}
}
else
{
lean_object* v___x_272_; 
lean_dec(v___x_258_);
lean_dec(v_val_255_);
v___x_272_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_272_;
}
}
}
else
{
lean_object* v___x_274_; 
lean_dec(v___x_254_);
v___x_274_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docCommentRange___boxed(lean_object* v_view_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_275_);
lean_dec_ref(v_view_275_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_docStringRange___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l_Lean_docStringRange___closed__0));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_docStringRange___closed__2(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_docStringRange___closed__1, &l_Lean_docStringRange___closed__1_once, _init_l_Lean_docStringRange___closed__1);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_docStringRange(lean_object* v_docComment_282_){
_start:
{
if (lean_obj_tag(v_docComment_282_) == 1)
{
lean_object* v_args_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_args_285_ = lean_ctor_get(v_docComment_282_, 2);
v___x_286_ = lean_array_get_size(v_args_285_);
v___x_287_ = lean_unsigned_to_nat(2u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
if (v___x_288_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_array_fget_borrowed(v_args_285_, v___x_289_);
if (lean_obj_tag(v___x_290_) == 1)
{
lean_object* v_args_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_args_291_ = lean_ctor_get(v___x_290_, 2);
v___x_292_ = lean_array_get_size(v_args_291_);
v___x_293_ = lean_nat_dec_eq(v___x_292_, v___x_287_);
if (v___x_293_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_array_fget_borrowed(v_args_285_, v___x_294_);
v___x_296_ = l_Lean_Syntax_getPos_x3f(v___x_295_, v___x_293_);
if (lean_obj_tag(v___x_296_) == 1)
{
lean_object* v_val_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_val_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = lean_array_fget_borrowed(v_args_291_, v___x_294_);
v___x_299_ = l_Lean_Syntax_getPos_x3f(v___x_298_, v___x_293_);
if (lean_obj_tag(v___x_299_) == 1)
{
lean_object* v_val_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_val_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = lean_array_fget_borrowed(v_args_291_, v___x_289_);
v___x_302_ = l_Lean_Syntax_getPos_x3f(v___x_301_, v___x_293_);
if (lean_obj_tag(v___x_302_) == 1)
{
lean_object* v_val_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_312_; 
v_val_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_312_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_val_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_312_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_val_300_);
lean_ctor_set(v___x_307_, 1, v_val_303_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_val_297_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_308_);
v___x_310_ = v___x_305_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
else
{
lean_object* v___x_313_; 
lean_dec(v___x_302_);
lean_dec(v_val_300_);
lean_dec(v_val_297_);
v___x_313_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__2);
return v___x_313_;
}
}
else
{
lean_object* v___x_314_; 
lean_dec(v___x_299_);
lean_dec(v_val_297_);
v___x_314_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__5);
return v___x_314_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v___x_296_);
v___x_315_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8, &l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8_once, _init_l___private_Lean_DocString_Add_0__Lean_docCommentRange___closed__8);
return v___x_315_;
}
}
}
else
{
goto v___jp_283_;
}
}
}
else
{
goto v___jp_283_;
}
v___jp_283_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_docStringRange___closed__2, &l_Lean_docStringRange___closed__2_once, _init_l_Lean_docStringRange___closed__2);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_docStringRange___boxed(lean_object* v_docComment_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_docStringRange(v_docComment_316_);
lean_dec(v_docComment_316_);
return v_res_317_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(uint8_t v_suppressElabErrors_326_, uint8_t v___x_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 1)
{
lean_object* v_pre_329_; 
v_pre_329_ = lean_ctor_get(v_x_328_, 0);
switch(lean_obj_tag(v_pre_329_))
{
case 1:
{
lean_object* v_pre_330_; 
v_pre_330_ = lean_ctor_get(v_pre_329_, 0);
switch(lean_obj_tag(v_pre_330_))
{
case 0:
{
lean_object* v_str_331_; lean_object* v_str_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_str_331_ = lean_ctor_get(v_x_328_, 1);
v_str_332_ = lean_ctor_get(v_pre_329_, 1);
v___x_333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_334_ = lean_string_dec_eq(v_str_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_336_ = lean_string_dec_eq(v_str_332_, v___x_335_);
if (v___x_336_ == 0)
{
return v___x_336_;
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_338_ = lean_string_dec_eq(v_str_331_, v___x_337_);
if (v___x_338_ == 0)
{
return v___x_338_;
}
else
{
return v_suppressElabErrors_326_;
}
}
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_340_ = lean_string_dec_eq(v_str_331_, v___x_339_);
if (v___x_340_ == 0)
{
return v___x_340_;
}
else
{
return v_suppressElabErrors_326_;
}
}
}
case 1:
{
lean_object* v_pre_341_; 
v_pre_341_ = lean_ctor_get(v_pre_330_, 0);
if (lean_obj_tag(v_pre_341_) == 0)
{
lean_object* v_str_342_; lean_object* v_str_343_; lean_object* v_str_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_str_342_ = lean_ctor_get(v_x_328_, 1);
v_str_343_ = lean_ctor_get(v_pre_329_, 1);
v_str_344_ = lean_ctor_get(v_pre_330_, 1);
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_346_ = lean_string_dec_eq(v_str_344_, v___x_345_);
if (v___x_346_ == 0)
{
return v___x_346_;
}
else
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_348_ = lean_string_dec_eq(v_str_343_, v___x_347_);
if (v___x_348_ == 0)
{
return v___x_348_;
}
else
{
lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_350_ = lean_string_dec_eq(v_str_342_, v___x_349_);
if (v___x_350_ == 0)
{
return v___x_350_;
}
else
{
return v_suppressElabErrors_326_;
}
}
}
}
else
{
return v___x_327_;
}
}
default: 
{
return v___x_327_;
}
}
}
case 0:
{
lean_object* v_str_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_str_351_ = lean_ctor_get(v_x_328_, 1);
v___x_352_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_353_ = lean_string_dec_eq(v_str_351_, v___x_352_);
if (v___x_353_ == 0)
{
return v___x_353_;
}
else
{
return v_suppressElabErrors_326_;
}
}
default: 
{
return v___x_327_;
}
}
}
else
{
return v___x_327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_354_, lean_object* v___x_355_, lean_object* v_x_356_){
_start:
{
uint8_t v_suppressElabErrors_boxed_357_; uint8_t v___x_3724__boxed_358_; uint8_t v_res_359_; lean_object* v_r_360_; 
v_suppressElabErrors_boxed_357_ = lean_unbox(v_suppressElabErrors_354_);
v___x_3724__boxed_358_ = lean_unbox(v___x_355_);
v_res_359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0(v_suppressElabErrors_boxed_357_, v___x_3724__boxed_358_, v_x_356_);
lean_dec(v_x_356_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v_as_363_, size_t v_sz_364_, size_t v_i_365_, lean_object* v_b_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_a_371_; uint8_t v___x_375_; 
v___x_375_ = lean_usize_dec_lt(v_i_365_, v_sz_364_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_dec_ref(v___x_361_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v_b_366_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v_snd_378_; lean_object* v_fst_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_446_; 
v_a_377_ = lean_array_uget(v_as_363_, v_i_365_);
v_snd_378_ = lean_ctor_get(v_a_377_, 1);
v_fst_379_ = lean_ctor_get(v_a_377_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_377_);
if (v_isSharedCheck_446_ == 0)
{
v___x_381_ = v_a_377_;
v_isShared_382_ = v_isSharedCheck_446_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_snd_378_);
lean_inc(v_fst_379_);
lean_dec(v_a_377_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_446_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v_snd_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_444_; 
v_snd_383_ = lean_ctor_get(v_snd_378_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_snd_378_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_snd_378_, 0);
lean_dec(v_unused_445_);
v___x_385_ = v_snd_378_;
v_isShared_386_ = v_isSharedCheck_444_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_snd_383_);
lean_dec(v_snd_378_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_444_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
uint8_t v_suppressElabErrors_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___y_391_; lean_object* v___y_392_; 
v_suppressElabErrors_387_ = lean_ctor_get_uint8(v___y_367_, sizeof(void*)*3 + 2);
v___x_388_ = lean_box(0);
lean_inc_ref(v___x_361_);
v___x_389_ = l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage(v___x_361_, v_fst_379_, v_snd_383_);
if (v_suppressElabErrors_387_ == 0)
{
v___y_391_ = v___y_367_;
v___y_392_ = v___y_368_;
goto v___jp_390_;
}
else
{
lean_object* v_data_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___f_442_; uint8_t v___x_443_; 
v_data_437_ = lean_ctor_get(v___x_389_, 4);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_dec_eq(v___x_362_, v___x_438_);
v___x_440_ = lean_box(v_suppressElabErrors_387_);
v___x_441_ = lean_box(v___x_439_);
v___f_442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_442_, 0, v___x_440_);
lean_closure_set(v___f_442_, 1, v___x_441_);
lean_inc(v_data_437_);
v___x_443_ = l_Lean_MessageData_hasTag(v___f_442_, v_data_437_);
if (v___x_443_ == 0)
{
lean_dec_ref(v___x_389_);
lean_del_object(v___x_385_);
lean_del_object(v___x_381_);
v_a_371_ = v___x_388_;
goto v___jp_370_;
}
else
{
v___y_391_ = v___y_367_;
v___y_392_ = v___y_368_;
goto v___jp_390_;
}
}
v___jp_390_:
{
lean_object* v_toCold_393_; lean_object* v_fileName_394_; lean_object* v_pos_395_; lean_object* v_endPos_396_; uint8_t v_keepFullRange_397_; uint8_t v_severity_398_; uint8_t v_isSilent_399_; lean_object* v_caption_400_; lean_object* v_data_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_436_; 
v_toCold_393_ = lean_ctor_get(v___y_391_, 0);
v_fileName_394_ = lean_ctor_get(v___x_389_, 0);
v_pos_395_ = lean_ctor_get(v___x_389_, 1);
v_endPos_396_ = lean_ctor_get(v___x_389_, 2);
v_keepFullRange_397_ = lean_ctor_get_uint8(v___x_389_, sizeof(void*)*5);
v_severity_398_ = lean_ctor_get_uint8(v___x_389_, sizeof(void*)*5 + 1);
v_isSilent_399_ = lean_ctor_get_uint8(v___x_389_, sizeof(void*)*5 + 2);
v_caption_400_ = lean_ctor_get(v___x_389_, 3);
v_data_401_ = lean_ctor_get(v___x_389_, 4);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_436_ == 0)
{
v___x_403_ = v___x_389_;
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_data_401_);
lean_inc(v_caption_400_);
lean_inc(v_endPos_396_);
lean_inc(v_pos_395_);
lean_inc(v_fileName_394_);
lean_dec(v___x_389_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_436_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v_currNamespace_405_; lean_object* v_openDecls_406_; lean_object* v___x_408_; 
v_currNamespace_405_ = lean_ctor_get(v_toCold_393_, 4);
v_openDecls_406_ = lean_ctor_get(v_toCold_393_, 5);
lean_inc(v_openDecls_406_);
lean_inc(v_currNamespace_405_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v_openDecls_406_);
lean_ctor_set(v___x_385_, 0, v_currNamespace_405_);
v___x_408_ = v___x_385_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_currNamespace_405_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_openDecls_406_);
v___x_408_ = v_reuseFailAlloc_435_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 4);
lean_ctor_set(v___x_381_, 1, v_data_401_);
lean_ctor_set(v___x_381_, 0, v___x_408_);
v___x_410_ = v___x_381_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_data_401_);
v___x_410_ = v_reuseFailAlloc_434_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 4, v___x_410_);
v___x_412_ = v___x_403_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fileName_394_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_pos_395_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_endPos_396_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_caption_400_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5, v_keepFullRange_397_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5 + 1, v_severity_398_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*5 + 2, v_isSilent_399_);
v___x_412_ = v_reuseFailAlloc_433_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v_env_414_; lean_object* v_nextMacroScope_415_; lean_object* v_ngen_416_; lean_object* v_auxDeclNGen_417_; lean_object* v_traceState_418_; lean_object* v_cache_419_; lean_object* v_recordedDeps_420_; lean_object* v_messages_421_; lean_object* v_infoState_422_; lean_object* v_snapshotTasks_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
v___x_413_ = lean_st_ref_take(v___y_392_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
v_nextMacroScope_415_ = lean_ctor_get(v___x_413_, 1);
v_ngen_416_ = lean_ctor_get(v___x_413_, 2);
v_auxDeclNGen_417_ = lean_ctor_get(v___x_413_, 3);
v_traceState_418_ = lean_ctor_get(v___x_413_, 4);
v_cache_419_ = lean_ctor_get(v___x_413_, 5);
v_recordedDeps_420_ = lean_ctor_get(v___x_413_, 6);
v_messages_421_ = lean_ctor_get(v___x_413_, 7);
v_infoState_422_ = lean_ctor_get(v___x_413_, 8);
v_snapshotTasks_423_ = lean_ctor_get(v___x_413_, 9);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_432_ == 0)
{
v___x_425_ = v___x_413_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_snapshotTasks_423_);
lean_inc(v_infoState_422_);
lean_inc(v_messages_421_);
lean_inc(v_recordedDeps_420_);
lean_inc(v_cache_419_);
lean_inc(v_traceState_418_);
lean_inc(v_auxDeclNGen_417_);
lean_inc(v_ngen_416_);
lean_inc(v_nextMacroScope_415_);
lean_inc(v_env_414_);
lean_dec(v___x_413_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_427_ = l_Lean_MessageLog_add(v___x_412_, v_messages_421_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 7, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_traceState_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_419_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_recordedDeps_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_infoState_422_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_snapshotTasks_423_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
v___x_430_ = lean_st_ref_put(v___y_392_, v___x_429_);
v_a_371_ = v___x_388_;
goto v___jp_370_;
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
v___jp_370_:
{
size_t v___x_372_; size_t v___x_373_; 
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_365_, v___x_372_);
v_i_365_ = v___x_373_;
v_b_366_ = v_a_371_;
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
lean_object* v_toCold_465_; lean_object* v_fileMap_466_; lean_object* v_fileName_467_; lean_object* v_currNamespace_468_; lean_object* v_openDecls_469_; lean_object* v_source_470_; lean_object* v___y_472_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_toCold_465_ = lean_ctor_get(v_a_462_, 0);
v_fileMap_466_ = lean_ctor_get(v_toCold_465_, 1);
v_fileName_467_ = lean_ctor_get(v_toCold_465_, 0);
v_currNamespace_468_ = lean_ctor_get(v_toCold_465_, 4);
v_openDecls_469_ = lean_ctor_get(v_toCold_465_, 5);
v_source_470_ = lean_ctor_get(v_fileMap_466_, 0);
v___x_513_ = lean_string_utf8_byte_size(v_source_470_);
v___x_514_ = lean_nat_dec_le(v_endPos_461_, v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_endPos_461_);
v___y_472_ = v___x_513_;
goto v___jp_471_;
}
else
{
v___y_472_ = v_endPos_461_;
goto v___jp_471_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v_env_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_473_ = lean_st_ref_get(v_a_463_);
v_env_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc_ref_n(v_env_474_, 2);
lean_dec(v___x_473_);
lean_inc(v___y_472_);
lean_inc_ref_n(v_fileMap_466_, 2);
lean_inc_ref(v_fileName_467_);
lean_inc_ref(v_source_470_);
v___x_475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_475_, 0, v_source_470_);
lean_ctor_set(v___x_475_, 1, v_fileName_467_);
lean_ctor_set(v___x_475_, 2, v_fileMap_466_);
lean_ctor_set(v___x_475_, 3, v___y_472_);
v___x_476_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_462_);
lean_inc(v_openDecls_469_);
lean_inc(v_currNamespace_468_);
v___x_477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_477_, 0, v_env_474_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v_currNamespace_468_);
lean_ctor_set(v___x_477_, 3, v_openDecls_469_);
lean_inc(v_startPos_460_);
v___x_478_ = l_Lean_Doc_Parser_BlockCtxt_forDocString(v_fileMap_466_, v_openPos_459_, v_startPos_460_, v___y_472_);
v___x_479_ = l_Lean_Parser_mkParserState(v_source_470_);
v___x_480_ = l_Lean_Parser_ParserState_setPos(v___x_479_, v_startPos_460_);
v___x_481_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_documentFn), 3, 1);
lean_closure_set(v___x_481_, 0, v___x_478_);
v___x_482_ = l_Lean_Parser_getTokenTable(v_env_474_);
lean_inc_ref(v___x_475_);
v___x_483_ = l_Lean_Parser_ParserFn_run(v___x_481_, v___x_475_, v___x_477_, v___x_482_, v___x_480_);
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
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0(v___x_475_, v___x_485_, v___x_484_, v_sz_489_, v___x_490_, v___x_488_, v_a_462_, v_a_463_);
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
lean_dec_ref_known(v___x_475_, 4);
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
lean_object* v___x_545_; lean_object* v_toCold_546_; lean_object* v_env_547_; lean_object* v_options_548_; uint8_t v___x_549_; lean_object* v_env_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_545_ = lean_st_ref_get(v___y_543_);
v_toCold_546_ = lean_ctor_get(v___y_542_, 0);
v_env_547_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_545_);
v_options_548_ = lean_ctor_get(v_toCold_546_, 2);
v___x_549_ = 0;
v_env_550_ = l_Lean_Environment_setRecordingDeps(v_env_547_, v___x_549_);
v___x_551_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__2);
v___x_552_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_548_);
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v_env_550_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
lean_ctor_set(v___x_553_, 2, v___x_552_);
lean_ctor_set(v___x_553_, 3, v_options_548_);
v___x_554_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_msgData_541_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___boxed(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msgData_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(lean_object* v_msg_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_ref_565_; lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_ref_565_ = lean_ctor_get(v___y_562_, 2);
v___x_566_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0(v_msg_561_, v___y_562_, v___y_563_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
lean_inc(v_ref_565_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_ref_565_);
lean_ctor_set(v___x_571_, 1, v_a_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 1);
lean_ctor_set(v___x_569_, 0, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg___boxed(lean_object* v_msg_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString(lean_object* v_docComment_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_____x_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___x_594_; 
v___x_594_ = l_Lean_docStringRange(v_docComment_581_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_595_, v_a_582_, v_a_583_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
else
{
lean_object* v_a_605_; 
v_a_605_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_594_, 1);
v_____x_586_ = v_a_605_;
v___y_587_ = v_a_582_;
v___y_588_ = v_a_583_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v_snd_589_; lean_object* v_fst_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; 
v_snd_589_ = lean_ctor_get(v_____x_586_, 1);
lean_inc(v_snd_589_);
v_fst_590_ = lean_ctor_get(v_____x_586_, 0);
lean_inc(v_fst_590_);
lean_dec_ref(v_____x_586_);
v_fst_591_ = lean_ctor_get(v_snd_589_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v_snd_589_, 1);
lean_inc(v_snd_592_);
lean_dec(v_snd_589_);
v___x_593_ = l_Lean_parseVersoDocStringAt(v_fst_590_, v_fst_591_, v_snd_592_, v___y_587_, v___y_588_);
lean_dec(v_fst_590_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseVersoDocString___boxed(lean_object* v_docComment_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_parseVersoDocString(v_docComment_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_docComment_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(lean_object* v_00_u03b1_611_, lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_msg_612_, v___y_613_, v___y_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___boxed(lean_object* v_00_u03b1_617_, lean_object* v_msg_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0(v_00_u03b1_617_, v_msg_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure(lean_object* v_view_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_____x_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___x_653_; 
v___x_653_ = l___private_Lean_DocString_Add_0__Lean_docCommentRange(v_view_623_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_throwError___at___00Lean_parseVersoDocString_spec__0___redArg(v_a_654_, v_a_624_, v_a_625_);
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_653_, 1);
v_____x_628_ = v_a_664_;
v___y_629_ = v_a_624_;
v___y_630_ = v_a_625_;
goto v___jp_627_;
}
v___jp_627_:
{
lean_object* v_snd_631_; lean_object* v_fst_632_; lean_object* v_fst_633_; lean_object* v_snd_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_snd_631_ = lean_ctor_get(v_____x_628_, 1);
lean_inc(v_snd_631_);
v_fst_632_ = lean_ctor_get(v_____x_628_, 0);
lean_inc(v_fst_632_);
lean_dec_ref(v_____x_628_);
v_fst_633_ = lean_ctor_get(v_snd_631_, 0);
lean_inc(v_fst_633_);
v_snd_634_ = lean_ctor_get(v_snd_631_, 1);
lean_inc(v_snd_634_);
lean_dec(v_snd_631_);
v___x_635_ = lean_box(0);
v___x_636_ = l_Lean_parseVersoDocStringAt(v_fst_632_, v_fst_633_, v_snd_634_, v___y_629_, v___y_630_);
lean_dec(v_fst_632_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v___x_636_, 0);
lean_dec(v_unused_644_);
v___x_638_ = v___x_636_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_dec(v___x_636_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_635_);
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_635_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_636_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_636_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_reportVersoParseFailure___boxed(lean_object* v_view_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_reportVersoParseFailure(v_view_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec_ref(v_view_665_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(lean_object* v_fileMap_x3f_670_, lean_object* v_declName_671_, lean_object* v_binders_672_, lean_object* v___x_673_, uint8_t v___x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
if (lean_obj_tag(v_fileMap_x3f_670_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Doc_DocM_exec___redArg(v_declName_671_, v_binders_672_, v___x_673_, v___x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_682_;
}
else
{
lean_object* v_toCold_683_; lean_object* v_val_684_; lean_object* v_currRecDepth_685_; lean_object* v_ref_686_; uint16_t v_optionFlags_687_; uint8_t v_suppressElabErrors_688_; uint8_t v_checkDeprecated_689_; uint8_t v_isRecordingDeps_690_; lean_object* v_fileName_691_; lean_object* v_options_692_; lean_object* v_maxRecDepth_693_; lean_object* v_currNamespace_694_; lean_object* v_openDecls_695_; lean_object* v_initHeartbeats_696_; lean_object* v_maxHeartbeats_697_; lean_object* v_quotContext_698_; lean_object* v_currMacroScope_699_; lean_object* v_cancelTk_x3f_700_; lean_object* v_inheritedTraceOptions_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_toCold_683_ = lean_ctor_get(v___y_679_, 0);
v_val_684_ = lean_ctor_get(v_fileMap_x3f_670_, 0);
v_currRecDepth_685_ = lean_ctor_get(v___y_679_, 1);
v_ref_686_ = lean_ctor_get(v___y_679_, 2);
v_optionFlags_687_ = lean_ctor_get_uint16(v___y_679_, sizeof(void*)*3);
v_suppressElabErrors_688_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*3 + 2);
v_checkDeprecated_689_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*3 + 3);
v_isRecordingDeps_690_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*3 + 4);
v_fileName_691_ = lean_ctor_get(v_toCold_683_, 0);
v_options_692_ = lean_ctor_get(v_toCold_683_, 2);
v_maxRecDepth_693_ = lean_ctor_get(v_toCold_683_, 3);
v_currNamespace_694_ = lean_ctor_get(v_toCold_683_, 4);
v_openDecls_695_ = lean_ctor_get(v_toCold_683_, 5);
v_initHeartbeats_696_ = lean_ctor_get(v_toCold_683_, 6);
v_maxHeartbeats_697_ = lean_ctor_get(v_toCold_683_, 7);
v_quotContext_698_ = lean_ctor_get(v_toCold_683_, 8);
v_currMacroScope_699_ = lean_ctor_get(v_toCold_683_, 9);
v_cancelTk_x3f_700_ = lean_ctor_get(v_toCold_683_, 10);
v_inheritedTraceOptions_701_ = lean_ctor_get(v_toCold_683_, 11);
lean_inc_ref(v_inheritedTraceOptions_701_);
lean_inc(v_cancelTk_x3f_700_);
lean_inc(v_currMacroScope_699_);
lean_inc(v_quotContext_698_);
lean_inc(v_maxHeartbeats_697_);
lean_inc(v_initHeartbeats_696_);
lean_inc(v_openDecls_695_);
lean_inc(v_currNamespace_694_);
lean_inc(v_maxRecDepth_693_);
lean_inc_ref(v_options_692_);
lean_inc(v_val_684_);
lean_inc_ref(v_fileName_691_);
v___x_702_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_702_, 0, v_fileName_691_);
lean_ctor_set(v___x_702_, 1, v_val_684_);
lean_ctor_set(v___x_702_, 2, v_options_692_);
lean_ctor_set(v___x_702_, 3, v_maxRecDepth_693_);
lean_ctor_set(v___x_702_, 4, v_currNamespace_694_);
lean_ctor_set(v___x_702_, 5, v_openDecls_695_);
lean_ctor_set(v___x_702_, 6, v_initHeartbeats_696_);
lean_ctor_set(v___x_702_, 7, v_maxHeartbeats_697_);
lean_ctor_set(v___x_702_, 8, v_quotContext_698_);
lean_ctor_set(v___x_702_, 9, v_currMacroScope_699_);
lean_ctor_set(v___x_702_, 10, v_cancelTk_x3f_700_);
lean_ctor_set(v___x_702_, 11, v_inheritedTraceOptions_701_);
lean_inc(v_ref_686_);
lean_inc(v_currRecDepth_685_);
v___x_703_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v_currRecDepth_685_);
lean_ctor_set(v___x_703_, 2, v_ref_686_);
lean_ctor_set_uint16(v___x_703_, sizeof(void*)*3, v_optionFlags_687_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*3 + 2, v_suppressElabErrors_688_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*3 + 3, v_checkDeprecated_689_);
lean_ctor_set_uint8(v___x_703_, sizeof(void*)*3 + 4, v_isRecordingDeps_690_);
v___x_704_ = l_Lean_Doc_DocM_exec___redArg(v_declName_671_, v_binders_672_, v___x_673_, v___x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___x_703_, v___y_680_);
lean_dec_ref_known(v___x_703_, 3);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_705_, lean_object* v_declName_706_, lean_object* v_binders_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
uint8_t v___x_9884__boxed_717_; lean_object* v_res_718_; 
v___x_9884__boxed_717_ = lean_unbox(v___x_709_);
v_res_718_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_705_, v_declName_706_, v_binders_707_, v___x_708_, v___x_9884__boxed_717_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v_fileMap_x3f_705_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_719_, size_t v_i_720_, lean_object* v_bs_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = lean_usize_dec_lt(v_i_720_, v_sz_719_);
if (v___x_722_ == 0)
{
return v_bs_721_;
}
else
{
lean_object* v_v_723_; lean_object* v___x_724_; lean_object* v_bs_x27_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v___x_728_; 
v_v_723_ = lean_array_uget(v_bs_721_, v_i_720_);
v___x_724_ = lean_unsigned_to_nat(0u);
v_bs_x27_725_ = lean_array_uset(v_bs_721_, v_i_720_, v___x_724_);
v___x_726_ = ((size_t)1ULL);
v___x_727_ = lean_usize_add(v_i_720_, v___x_726_);
v___x_728_ = lean_array_uset(v_bs_x27_725_, v_i_720_, v_v_723_);
v_i_720_ = v___x_727_;
v_bs_721_ = v___x_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_730_, lean_object* v_i_731_, lean_object* v_bs_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_730_);
lean_dec(v_sz_730_);
v_i_boxed_734_ = lean_unbox_usize(v_i_731_);
lean_dec(v_i_731_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_733_, v_i_boxed_734_, v_bs_732_);
return v_res_735_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_736_, lean_object* v_opt_737_){
_start:
{
lean_object* v_name_738_; lean_object* v_defValue_739_; lean_object* v_map_740_; lean_object* v___x_741_; 
v_name_738_ = lean_ctor_get(v_opt_737_, 0);
v_defValue_739_ = lean_ctor_get(v_opt_737_, 1);
v_map_740_ = lean_ctor_get(v_opts_736_, 0);
v___x_741_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_740_, v_name_738_);
if (lean_obj_tag(v___x_741_) == 0)
{
uint8_t v___x_742_; 
v___x_742_ = lean_unbox(v_defValue_739_);
return v___x_742_;
}
else
{
lean_object* v_val_743_; 
v_val_743_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v___x_741_, 1);
if (lean_obj_tag(v_val_743_) == 1)
{
uint8_t v_v_744_; 
v_v_744_ = lean_ctor_get_uint8(v_val_743_, 0);
lean_dec_ref_known(v_val_743_, 0);
return v_v_744_;
}
else
{
uint8_t v___x_745_; 
lean_dec(v_val_743_);
v___x_745_ = lean_unbox(v_defValue_739_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_746_, lean_object* v_opt_747_){
_start:
{
uint8_t v_res_748_; lean_object* v_r_749_; 
v_res_748_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_746_, v_opt_747_);
lean_dec_ref(v_opt_747_);
lean_dec_ref(v_opts_746_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v_env_757_; uint8_t v___x_758_; lean_object* v_env_759_; lean_object* v___x_760_; lean_object* v_toCold_761_; lean_object* v_mctx_762_; lean_object* v_lctx_763_; lean_object* v_options_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_756_ = lean_st_ref_get(v___y_754_);
v_env_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_ref(v_env_757_);
lean_dec(v___x_756_);
v___x_758_ = 0;
v_env_759_ = l_Lean_Environment_setRecordingDeps(v_env_757_, v___x_758_);
v___x_760_ = lean_st_ref_get(v___y_752_);
v_toCold_761_ = lean_ctor_get(v___y_753_, 0);
v_mctx_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_mctx_762_);
lean_dec(v___x_760_);
v_lctx_763_ = lean_ctor_get(v___y_751_, 2);
v_options_764_ = lean_ctor_get(v_toCold_761_, 2);
lean_inc_ref(v_options_764_);
lean_inc_ref(v_lctx_763_);
v___x_765_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_765_, 0, v_env_759_);
lean_ctor_set(v___x_765_, 1, v_mctx_762_);
lean_ctor_set(v___x_765_, 2, v_lctx_763_);
lean_ctor_set(v___x_765_, 3, v_options_764_);
v___x_766_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_msgData_750_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_774_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 1)
{
lean_object* v_pre_777_; 
v_pre_777_ = lean_ctor_get(v_x_776_, 0);
switch(lean_obj_tag(v_pre_777_))
{
case 1:
{
lean_object* v_pre_778_; 
v_pre_778_ = lean_ctor_get(v_pre_777_, 0);
switch(lean_obj_tag(v_pre_778_))
{
case 0:
{
lean_object* v_str_779_; lean_object* v_str_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_str_779_ = lean_ctor_get(v_x_776_, 1);
v_str_780_ = lean_ctor_get(v_pre_777_, 1);
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__0));
v___x_782_ = lean_string_dec_eq(v_str_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__1));
v___x_784_ = lean_string_dec_eq(v_str_780_, v___x_783_);
if (v___x_784_ == 0)
{
return v___x_784_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__2));
v___x_786_ = lean_string_dec_eq(v_str_779_, v___x_785_);
if (v___x_786_ == 0)
{
return v___x_786_;
}
else
{
return v_suppressElabErrors_775_;
}
}
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__3));
v___x_788_ = lean_string_dec_eq(v_str_779_, v___x_787_);
if (v___x_788_ == 0)
{
return v___x_788_;
}
else
{
return v_suppressElabErrors_775_;
}
}
}
case 1:
{
lean_object* v_pre_789_; 
v_pre_789_ = lean_ctor_get(v_pre_778_, 0);
if (lean_obj_tag(v_pre_789_) == 0)
{
lean_object* v_str_790_; lean_object* v_str_791_; lean_object* v_str_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_str_790_ = lean_ctor_get(v_x_776_, 1);
v_str_791_ = lean_ctor_get(v_pre_777_, 1);
v_str_792_ = lean_ctor_get(v_pre_778_, 1);
v___x_793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__4));
v___x_794_ = lean_string_dec_eq(v_str_792_, v___x_793_);
if (v___x_794_ == 0)
{
return v___x_794_;
}
else
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__5));
v___x_796_ = lean_string_dec_eq(v_str_791_, v___x_795_);
if (v___x_796_ == 0)
{
return v___x_796_;
}
else
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__6));
v___x_798_ = lean_string_dec_eq(v_str_790_, v___x_797_);
if (v___x_798_ == 0)
{
return v___x_798_;
}
else
{
return v_suppressElabErrors_775_;
}
}
}
}
else
{
uint8_t v___x_799_; 
v___x_799_ = 0;
return v___x_799_;
}
}
default: 
{
uint8_t v___x_800_; 
v___x_800_ = 0;
return v___x_800_;
}
}
}
case 0:
{
lean_object* v_str_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_str_801_ = lean_ctor_get(v_x_776_, 1);
v___x_802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_803_ = lean_string_dec_eq(v_str_801_, v___x_802_);
if (v___x_803_ == 0)
{
return v___x_803_;
}
else
{
return v_suppressElabErrors_775_;
}
}
default: 
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
}
else
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_806_, lean_object* v_x_807_){
_start:
{
uint8_t v_suppressElabErrors_boxed_808_; uint8_t v_res_809_; lean_object* v_r_810_; 
v_suppressElabErrors_boxed_808_ = lean_unbox(v_suppressElabErrors_806_);
v_res_809_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_808_, v_x_807_);
lean_dec(v_x_807_);
v_r_810_ = lean_box(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_811_, lean_object* v_msgData_812_, uint8_t v_severity_813_, uint8_t v_isSilent_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___y_821_; uint8_t v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; uint8_t v___y_827_; lean_object* v_toCold_828_; lean_object* v___y_829_; lean_object* v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; uint8_t v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; uint8_t v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; uint8_t v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; lean_object* v___y_891_; uint8_t v___y_895_; uint8_t v___y_896_; uint8_t v___x_906_; uint8_t v___y_908_; uint8_t v___x_914_; 
v___x_906_ = 2;
v___x_914_ = l_Lean_instBEqMessageSeverity_beq(v_severity_813_, v___x_906_);
if (v___x_914_ == 0)
{
v___y_908_ = v___x_914_;
goto v___jp_907_;
}
else
{
uint8_t v___x_915_; 
lean_inc_ref(v_msgData_812_);
v___x_915_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_812_);
if (v___x_915_ == 0)
{
v___y_908_ = v___x_915_;
goto v___jp_907_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_msgData_812_);
v___x_916_ = lean_box(0);
v___x_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
return v___x_917_;
}
}
v___jp_820_:
{
lean_object* v_currNamespace_830_; lean_object* v_openDecls_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_env_836_; lean_object* v_nextMacroScope_837_; lean_object* v_ngen_838_; lean_object* v_auxDeclNGen_839_; lean_object* v_traceState_840_; lean_object* v_cache_841_; lean_object* v_recordedDeps_842_; lean_object* v_messages_843_; lean_object* v_infoState_844_; lean_object* v_snapshotTasks_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_856_; 
v_currNamespace_830_ = lean_ctor_get(v_toCold_828_, 4);
v_openDecls_831_ = lean_ctor_get(v_toCold_828_, 5);
lean_inc(v_openDecls_831_);
lean_inc(v_currNamespace_830_);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_currNamespace_830_);
lean_ctor_set(v___x_832_, 1, v_openDecls_831_);
v___x_833_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v___y_823_);
lean_inc_ref(v___y_824_);
lean_inc_ref(v___y_826_);
v___x_834_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_834_, 0, v___y_826_);
lean_ctor_set(v___x_834_, 1, v___y_825_);
lean_ctor_set(v___x_834_, 2, v___y_821_);
lean_ctor_set(v___x_834_, 3, v___y_824_);
lean_ctor_set(v___x_834_, 4, v___x_833_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*5, v___y_822_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*5 + 1, v___y_827_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*5 + 2, v_isSilent_814_);
v___x_835_ = lean_st_ref_take(v___y_829_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
v_nextMacroScope_837_ = lean_ctor_get(v___x_835_, 1);
v_ngen_838_ = lean_ctor_get(v___x_835_, 2);
v_auxDeclNGen_839_ = lean_ctor_get(v___x_835_, 3);
v_traceState_840_ = lean_ctor_get(v___x_835_, 4);
v_cache_841_ = lean_ctor_get(v___x_835_, 5);
v_recordedDeps_842_ = lean_ctor_get(v___x_835_, 6);
v_messages_843_ = lean_ctor_get(v___x_835_, 7);
v_infoState_844_ = lean_ctor_get(v___x_835_, 8);
v_snapshotTasks_845_ = lean_ctor_get(v___x_835_, 9);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_856_ == 0)
{
v___x_847_ = v___x_835_;
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snapshotTasks_845_);
lean_inc(v_infoState_844_);
lean_inc(v_messages_843_);
lean_inc(v_recordedDeps_842_);
lean_inc(v_cache_841_);
lean_inc(v_traceState_840_);
lean_inc(v_auxDeclNGen_839_);
lean_inc(v_ngen_838_);
lean_inc(v_nextMacroScope_837_);
lean_inc(v_env_836_);
lean_dec(v___x_835_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_856_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = lean_box(0);
v___x_850_ = l_Lean_MessageLog_add(v___x_834_, v_messages_843_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 7, v___x_850_);
v___x_852_ = v___x_847_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_env_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_nextMacroScope_837_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_ngen_838_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_auxDeclNGen_839_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_traceState_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 5, v_cache_841_);
lean_ctor_set(v_reuseFailAlloc_855_, 6, v_recordedDeps_842_);
lean_ctor_set(v_reuseFailAlloc_855_, 7, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_855_, 8, v_infoState_844_);
lean_ctor_set(v_reuseFailAlloc_855_, 9, v_snapshotTasks_845_);
v___x_852_ = v_reuseFailAlloc_855_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_st_ref_put(v___y_829_, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_849_);
return v___x_854_;
}
}
}
v___jp_857_:
{
lean_object* v_fileName_866_; lean_object* v_fileMap_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_883_; 
v_fileName_866_ = lean_ctor_get(v___y_864_, 0);
v_fileMap_867_ = lean_ctor_get(v___y_864_, 1);
v___x_868_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_812_);
v___x_869_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_868_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_883_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_883_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_883_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc_ref_n(v_fileMap_867_, 2);
v___x_874_ = l_Lean_FileMap_toPosition(v_fileMap_867_, v___y_862_);
lean_dec(v___y_862_);
v___x_875_ = l_Lean_FileMap_toPosition(v_fileMap_867_, v___y_865_);
lean_dec(v___y_865_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
v___x_877_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_861_ == 0)
{
lean_del_object(v___x_872_);
lean_dec_ref(v___y_858_);
v___y_821_ = v___x_876_;
v___y_822_ = v___y_860_;
v___y_823_ = v_a_870_;
v___y_824_ = v___x_877_;
v___y_825_ = v___x_874_;
v___y_826_ = v_fileName_866_;
v___y_827_ = v___y_863_;
v_toCold_828_ = v___y_859_;
v___y_829_ = v___y_818_;
goto v___jp_820_;
}
else
{
uint8_t v___x_878_; 
lean_inc(v_a_870_);
v___x_878_ = l_Lean_MessageData_hasTag(v___y_858_, v_a_870_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_876_, 1);
lean_dec_ref(v___x_874_);
lean_dec(v_a_870_);
v___x_879_ = lean_box(0);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_879_);
v___x_881_ = v___x_872_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_del_object(v___x_872_);
v___y_821_ = v___x_876_;
v___y_822_ = v___y_860_;
v___y_823_ = v_a_870_;
v___y_824_ = v___x_877_;
v___y_825_ = v___x_874_;
v___y_826_ = v_fileName_866_;
v___y_827_ = v___y_863_;
v_toCold_828_ = v___y_859_;
v___y_829_ = v___y_818_;
goto v___jp_820_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Syntax_getTailPos_x3f(v___y_889_, v___y_888_);
lean_dec(v___y_889_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_inc(v___y_891_);
v___y_858_ = v___y_886_;
v___y_859_ = v___y_887_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_885_;
v___y_862_ = v___y_891_;
v___y_863_ = v___y_890_;
v___y_864_ = v___y_887_;
v___y_865_ = v___y_891_;
goto v___jp_857_;
}
else
{
lean_object* v_val_893_; 
v_val_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_val_893_);
lean_dec_ref_known(v___x_892_, 1);
v___y_858_ = v___y_886_;
v___y_859_ = v___y_887_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_885_;
v___y_862_ = v___y_891_;
v___y_863_ = v___y_890_;
v___y_864_ = v___y_887_;
v___y_865_ = v_val_893_;
goto v___jp_857_;
}
}
v___jp_894_:
{
lean_object* v_toCold_897_; lean_object* v_ref_898_; uint8_t v_suppressElabErrors_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v_ref_902_; lean_object* v___x_903_; 
v_toCold_897_ = lean_ctor_get(v___y_817_, 0);
v_ref_898_ = lean_ctor_get(v___y_817_, 2);
v_suppressElabErrors_899_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*3 + 2);
v___x_900_ = lean_box(v_suppressElabErrors_899_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_901_, 0, v___x_900_);
v_ref_902_ = l_Lean_replaceRef(v_ref_811_, v_ref_898_);
v___x_903_ = l_Lean_Syntax_getPos_x3f(v_ref_902_, v___y_895_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_885_ = v_suppressElabErrors_899_;
v___y_886_ = v___f_901_;
v___y_887_ = v_toCold_897_;
v___y_888_ = v___y_895_;
v___y_889_ = v_ref_902_;
v___y_890_ = v___y_896_;
v___y_891_ = v___x_904_;
goto v___jp_884_;
}
else
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v___x_903_, 1);
v___y_885_ = v_suppressElabErrors_899_;
v___y_886_ = v___f_901_;
v___y_887_ = v_toCold_897_;
v___y_888_ = v___y_895_;
v___y_889_ = v_ref_902_;
v___y_890_ = v___y_896_;
v___y_891_ = v_val_905_;
goto v___jp_884_;
}
}
v___jp_907_:
{
uint8_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 1;
v___x_910_ = l_Lean_instBEqMessageSeverity_beq(v_severity_813_, v___x_909_);
if (v___x_910_ == 0)
{
v___y_895_ = v___y_908_;
v___y_896_ = v_severity_813_;
goto v___jp_894_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_911_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_817_);
v___x_912_ = l_Lean_warningAsError;
v___x_913_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_911_, v___x_912_);
lean_dec_ref(v___x_911_);
if (v___x_913_ == 0)
{
v___y_895_ = v___y_908_;
v___y_896_ = v_severity_813_;
goto v___jp_894_;
}
else
{
v___y_895_ = v___y_908_;
v___y_896_ = v___x_906_;
goto v___jp_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_918_, lean_object* v_msgData_919_, lean_object* v_severity_920_, lean_object* v_isSilent_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v_severity_boxed_927_; uint8_t v_isSilent_boxed_928_; lean_object* v_res_929_; 
v_severity_boxed_927_ = lean_unbox(v_severity_920_);
v_isSilent_boxed_928_ = lean_unbox(v_isSilent_921_);
v_res_929_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_918_, v_msgData_919_, v_severity_boxed_927_, v_isSilent_boxed_928_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v_ref_918_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_933_);
return v___x_942_;
}
else
{
lean_object* v_ref_943_; lean_object* v_a_944_; uint8_t v_severity_945_; uint8_t v_isSilent_946_; lean_object* v_data_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_ref_943_ = lean_ctor_get(v___y_938_, 2);
v_a_944_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
v_severity_945_ = lean_ctor_get_uint8(v_a_944_, sizeof(void*)*5 + 1);
v_isSilent_946_ = lean_ctor_get_uint8(v_a_944_, sizeof(void*)*5 + 2);
v_data_947_ = lean_ctor_get(v_a_944_, 4);
v___x_948_ = lean_box(0);
lean_inc(v_data_947_);
v___x_949_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_943_, v_data_947_, v_severity_945_, v_isSilent_946_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_949_) == 0)
{
size_t v___x_950_; size_t v___x_951_; 
lean_dec_ref_known(v___x_949_, 1);
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_932_, v___x_950_);
v_i_932_ = v___x_951_;
v_b_933_ = v___x_948_;
goto _start;
}
else
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_953_, lean_object* v_sz_954_, lean_object* v_i_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_sz_boxed_964_ = lean_unbox_usize(v_sz_954_);
lean_dec(v_sz_954_);
v_i_boxed_965_ = lean_unbox_usize(v_i_955_);
lean_dec(v_i_955_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_953_, v_sz_boxed_964_, v_i_boxed_965_, v_b_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v_as_953_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_infoState_971_; lean_object* v_env_972_; lean_object* v_nextMacroScope_973_; lean_object* v_ngen_974_; lean_object* v_auxDeclNGen_975_; lean_object* v_traceState_976_; lean_object* v_cache_977_; lean_object* v_recordedDeps_978_; lean_object* v_messages_979_; lean_object* v_snapshotTasks_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1000_; 
v___x_970_ = lean_st_ref_take(v___y_968_);
v_infoState_971_ = lean_ctor_get(v___x_970_, 8);
v_env_972_ = lean_ctor_get(v___x_970_, 0);
v_nextMacroScope_973_ = lean_ctor_get(v___x_970_, 1);
v_ngen_974_ = lean_ctor_get(v___x_970_, 2);
v_auxDeclNGen_975_ = lean_ctor_get(v___x_970_, 3);
v_traceState_976_ = lean_ctor_get(v___x_970_, 4);
v_cache_977_ = lean_ctor_get(v___x_970_, 5);
v_recordedDeps_978_ = lean_ctor_get(v___x_970_, 6);
v_messages_979_ = lean_ctor_get(v___x_970_, 7);
v_snapshotTasks_980_ = lean_ctor_get(v___x_970_, 9);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_982_ = v___x_970_;
v_isShared_983_ = v_isSharedCheck_1000_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snapshotTasks_980_);
lean_inc(v_infoState_971_);
lean_inc(v_messages_979_);
lean_inc(v_recordedDeps_978_);
lean_inc(v_cache_977_);
lean_inc(v_traceState_976_);
lean_inc(v_auxDeclNGen_975_);
lean_inc(v_ngen_974_);
lean_inc(v_nextMacroScope_973_);
lean_inc(v_env_972_);
lean_dec(v___x_970_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1000_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_assignment_984_; lean_object* v_lazyAssignment_985_; lean_object* v_trees_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_999_; 
v_assignment_984_ = lean_ctor_get(v_infoState_971_, 0);
v_lazyAssignment_985_ = lean_ctor_get(v_infoState_971_, 1);
v_trees_986_ = lean_ctor_get(v_infoState_971_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v_infoState_971_);
if (v_isSharedCheck_999_ == 0)
{
v___x_988_ = v_infoState_971_;
v_isShared_989_ = v_isSharedCheck_999_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_trees_986_);
lean_inc(v_lazyAssignment_985_);
lean_inc(v_assignment_984_);
lean_dec(v_infoState_971_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_999_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_box(0);
if (v_isShared_989_ == 0)
{
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_assignment_984_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_lazyAssignment_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_trees_986_);
v___x_992_ = v_reuseFailAlloc_998_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*3, v_flag_967_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 8, v___x_992_);
v___x_994_ = v___x_982_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_env_972_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_973_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_974_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_975_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_traceState_976_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_cache_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_recordedDeps_978_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_messages_979_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_997_, 9, v_snapshotTasks_980_);
v___x_994_ = v_reuseFailAlloc_997_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_st_ref_put(v___y_968_, v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_990_);
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_flag_boxed_1004_; lean_object* v_res_1005_; 
v_flag_boxed_1004_ = lean_unbox(v_flag_1001_);
v_res_1005_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1004_, v___y_1002_);
lean_dec(v___y_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v_infoState_1016_; uint8_t v_enabled_1017_; lean_object* v_a_1019_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1015_ = lean_st_ref_get(v___y_1013_);
v_infoState_1016_ = lean_ctor_get(v___x_1015_, 8);
lean_inc_ref(v_infoState_1016_);
lean_dec(v___x_1015_);
v_enabled_1017_ = lean_ctor_get_uint8(v_infoState_1016_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1016_);
v___x_1029_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1006_, v___y_1013_);
lean_dec_ref(v___x_1029_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
v___x_1030_ = lean_apply_7(v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, lean_box(0));
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref_known(v___x_1030_, 1);
v___x_1032_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1017_, v___y_1013_);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_1032_, 0);
lean_dec(v_unused_1040_);
v___x_1034_ = v___x_1032_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v___x_1032_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_a_1031_);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1031_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1041_; 
v_a_1041_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1030_, 1);
v_a_1019_ = v_a_1041_;
goto v___jp_1018_;
}
v___jp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v___x_1020_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1017_, v___y_1013_);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v___x_1020_, 0);
lean_dec(v_unused_1028_);
v___x_1022_ = v___x_1020_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v___x_1020_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set_tag(v___x_1022_, 1);
lean_ctor_set(v___x_1022_, 0, v_a_1019_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1019_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
uint8_t v_flag_boxed_1051_; lean_object* v_res_1052_; 
v_flag_boxed_1051_ = lean_unbox(v_flag_1042_);
v_res_1052_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1051_, v_x_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1053_, lean_object* v_binders_1054_, lean_object* v_blocks_1055_, lean_object* v_fileMap_x3f_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1062_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_a_1067_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___y_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v_sz_1085_ = lean_array_size(v_blocks_1055_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1085_, v___x_1086_, v_blocks_1055_);
v___x_1088_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = 1;
v___x_1090_ = lean_box(v___x_1089_);
v___y_1091_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1091_, 0, v_fileMap_x3f_1056_);
lean_closure_set(v___y_1091_, 1, v_declName_1053_);
lean_closure_set(v___y_1091_, 2, v_binders_1054_);
lean_closure_set(v___y_1091_, 3, v___x_1088_);
lean_closure_set(v___y_1091_, 4, v___x_1090_);
v___x_1092_ = 0;
v___x_1093_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1092_, v___y_1091_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___x_1095_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1062_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = l_Lean_Core_setMessageLog___redArg(v_a_1065_, v_a_1062_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; size_t v_sz_1100_; lean_object* v___x_1101_; 
lean_dec_ref_known(v___x_1097_, 1);
v___x_1098_ = l_Lean_MessageLog_toArray(v_a_1096_);
lean_dec(v_a_1096_);
v___x_1099_ = lean_box(0);
v_sz_1100_ = lean_array_size(v___x_1098_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1098_, v_sz_1100_, v___x_1086_, v___x_1099_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec_ref(v___x_1098_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1101_, 0);
lean_dec(v_unused_1127_);
v___x_1103_ = v___x_1101_;
v_isShared_1104_ = v_isSharedCheck_1126_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v___x_1101_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1126_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1125_; 
v_fst_1105_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1106_ = lean_ctor_get(v_a_1094_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1108_ = v_a_1094_;
v_isShared_1109_ = v_isSharedCheck_1125_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snd_1106_);
lean_inc(v_fst_1105_);
lean_dec(v_a_1094_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1125_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1124_; 
v_fst_1110_ = lean_ctor_get(v_fst_1105_, 0);
v_snd_1111_ = lean_ctor_get(v_fst_1105_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_fst_1105_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1113_ = v_fst_1105_;
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_fst_1105_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1124_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1110_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_snd_1111_);
v___x_1116_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1116_);
v___x_1118_ = v___x_1108_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1106_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1118_);
v___x_1120_ = v___x_1103_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_a_1094_);
v_a_1128_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1101_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1101_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_a_1096_);
lean_dec(v_a_1094_);
v_a_1136_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1097_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1097_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1144_; 
lean_dec(v_a_1094_);
v_a_1144_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1095_, 1);
v_a_1067_ = v_a_1144_;
goto v___jp_1066_;
}
}
else
{
lean_object* v_a_1145_; 
v_a_1145_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1093_, 1);
v_a_1067_ = v_a_1145_;
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Core_setMessageLog___redArg(v_a_1065_, v_a_1062_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1068_, 0);
lean_dec(v_unused_1076_);
v___x_1070_ = v___x_1068_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1068_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 0, v_a_1067_);
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1067_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_a_1067_);
v_a_1077_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1068_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1068_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_fileMap_x3f_1056_);
lean_dec_ref(v_blocks_1055_);
lean_dec(v_binders_1054_);
lean_dec(v_declName_1053_);
v_a_1146_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1064_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1064_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
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
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1154_, lean_object* v_binders_1155_, lean_object* v_blocks_1156_, lean_object* v_fileMap_x3f_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1154_, v_binders_1155_, v_blocks_1156_, v_fileMap_x3f_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1166_, v___y_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_flag_boxed_1183_; lean_object* v_res_1184_; 
v_flag_boxed_1183_ = lean_unbox(v_flag_1175_);
v_res_1184_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1183_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1185_, uint8_t v_flag_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1196_, lean_object* v_flag_1197_, lean_object* v_x_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_flag_boxed_1206_; lean_object* v_res_1207_; 
v_flag_boxed_1206_ = lean_unbox(v_flag_1197_);
v_res_1207_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1196_, v_flag_boxed_1206_, v_x_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1208_, lean_object* v_msgData_1209_, uint8_t v_severity_1210_, uint8_t v_isSilent_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1208_, v_msgData_1209_, v_severity_1210_, v_isSilent_1211_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1220_, lean_object* v_msgData_1221_, lean_object* v_severity_1222_, lean_object* v_isSilent_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
uint8_t v_severity_boxed_1231_; uint8_t v_isSilent_boxed_1232_; lean_object* v_res_1233_; 
v_severity_boxed_1231_ = lean_unbox(v_severity_1222_);
v_isSilent_boxed_1232_ = lean_unbox(v_isSilent_1223_);
v_res_1233_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1220_, v_msgData_1221_, v_severity_boxed_1231_, v_isSilent_boxed_1232_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v_ref_1220_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1234_, uint8_t v_severity_1235_, uint8_t v_isSilent_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_ref_1242_; lean_object* v___x_1243_; 
v_ref_1242_ = lean_ctor_get(v___y_1239_, 2);
v___x_1243_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1242_, v_msgData_1234_, v_severity_1235_, v_isSilent_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1244_, lean_object* v_severity_1245_, lean_object* v_isSilent_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_severity_boxed_1252_; uint8_t v_isSilent_boxed_1253_; lean_object* v_res_1254_; 
v_severity_boxed_1252_ = lean_unbox(v_severity_1245_);
v_isSilent_boxed_1253_ = lean_unbox(v_isSilent_1246_);
v_res_1254_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1244_, v_severity_boxed_1252_, v_isSilent_boxed_1253_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = 2;
v___x_1264_ = 0;
v___x_1265_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1255_, v___x_1263_, v___x_1264_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1275_, size_t v_sz_1276_, size_t v_i_1277_, lean_object* v_b_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_usize_dec_lt(v_i_1277_, v_sz_1276_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_b_1278_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v_snd_1289_; lean_object* v_snd_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_a_1288_ = lean_array_uget_borrowed(v_as_1275_, v_i_1277_);
v_snd_1289_ = lean_ctor_get(v_a_1288_, 1);
v_snd_1290_ = lean_ctor_get(v_snd_1289_, 1);
v___x_1291_ = lean_box(0);
lean_inc(v_snd_1290_);
v___x_1292_ = l_Lean_Parser_Error_toString(v_snd_1290_);
v___x_1293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
v___x_1294_ = l_Lean_MessageData_ofFormat(v___x_1293_);
v___x_1295_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1294_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1295_) == 0)
{
size_t v___x_1296_; size_t v___x_1297_; 
lean_dec_ref_known(v___x_1295_, 1);
v___x_1296_ = ((size_t)1ULL);
v___x_1297_ = lean_usize_add(v_i_1277_, v___x_1296_);
v_i_1277_ = v___x_1297_;
v_b_1278_ = v___x_1291_;
goto _start;
}
else
{
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1299_, lean_object* v_sz_1300_, lean_object* v_i_1301_, lean_object* v_b_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1300_);
lean_dec(v_sz_1300_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1299_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec_ref(v_as_1299_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1331_, lean_object* v_binders_1332_, lean_object* v_docComment_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v_toCold_1342_; lean_object* v_env_1343_; lean_object* v_fileName_1344_; lean_object* v_currNamespace_1345_; lean_object* v_openDecls_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1341_ = lean_st_ref_get(v_a_1339_);
v_toCold_1342_ = lean_ctor_get(v_a_1338_, 0);
v_env_1343_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref_n(v_env_1343_, 2);
lean_dec(v___x_1341_);
v_fileName_1344_ = lean_ctor_get(v_toCold_1342_, 0);
v_currNamespace_1345_ = lean_ctor_get(v_toCold_1342_, 4);
v_openDecls_1346_ = lean_ctor_get(v_toCold_1342_, 5);
v___x_1347_ = lean_string_utf8_byte_size(v_docComment_1333_);
lean_inc_ref_n(v_docComment_1333_, 2);
v___x_1348_ = l_Lean_FileMap_ofString(v_docComment_1333_);
lean_inc_ref(v___x_1348_);
lean_inc_ref(v_fileName_1344_);
v___x_1349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1349_, 0, v_docComment_1333_);
lean_ctor_set(v___x_1349_, 1, v_fileName_1344_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
lean_ctor_set(v___x_1349_, 3, v___x_1347_);
v___x_1350_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1338_);
lean_inc(v_openDecls_1346_);
lean_inc(v_currNamespace_1345_);
v___x_1351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1351_, 0, v_env_1343_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
lean_ctor_set(v___x_1351_, 2, v_currNamespace_1345_);
lean_ctor_set(v___x_1351_, 3, v_openDecls_1346_);
v___x_1352_ = l_Lean_Parser_mkParserState(v_docComment_1333_);
lean_dec_ref(v_docComment_1333_);
v___x_1353_ = lean_unsigned_to_nat(0u);
v___x_1354_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1355_ = l_Lean_Parser_getTokenTable(v_env_1343_);
v___x_1356_ = l_Lean_Parser_ParserFn_run(v___x_1354_, v___x_1349_, v___x_1351_, v___x_1355_, v___x_1352_);
lean_inc_ref(v___x_1356_);
v___x_1357_ = l_Lean_Parser_ParserState_allErrors(v___x_1356_);
v___x_1358_ = lean_array_get_size(v___x_1357_);
v___x_1359_ = lean_nat_dec_eq(v___x_1358_, v___x_1353_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___x_1356_);
lean_dec_ref(v___x_1348_);
lean_dec(v_binders_1332_);
lean_dec(v_declName_1331_);
v___x_1360_ = lean_box(0);
v_sz_1361_ = lean_array_size(v___x_1357_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1357_, v_sz_1361_, v___x_1362_, v___x_1360_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec_ref(v___x_1357_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1372_);
v___x_1365_ = v___x_1363_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v___x_1363_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_a_1373_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1363_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1363_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_stxStack_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v___x_1357_);
v_stxStack_1381_ = lean_ctor_get(v___x_1356_, 0);
lean_inc_ref(v_stxStack_1381_);
lean_dec_ref(v___x_1356_);
v___x_1382_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1381_);
lean_dec_ref(v_stxStack_1381_);
v___x_1383_ = l_Lean_TSyntax_getVersoBlocks(v___x_1382_);
lean_dec(v___x_1382_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1348_);
v___x_1385_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1331_, v_binders_1332_, v___x_1383_, v___x_1384_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1386_, lean_object* v_binders_1387_, lean_object* v_docComment_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_versoDocStringOfText(v_declName_1386_, v_binders_1387_, v_docComment_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1397_, uint8_t v_severity_1398_, uint8_t v_isSilent_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1397_, v_severity_1398_, v_isSilent_1399_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1408_, lean_object* v_severity_1409_, lean_object* v_isSilent_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_severity_boxed_1418_; uint8_t v_isSilent_boxed_1419_; lean_object* v_res_1420_; 
v_severity_boxed_1418_ = lean_unbox(v_severity_1409_);
v_isSilent_boxed_1419_ = lean_unbox(v_isSilent_1410_);
v_res_1420_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1408_, v_severity_boxed_1418_, v_isSilent_boxed_1419_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1430_, lean_object* v_binders_1431_, lean_object* v_docComment_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_docStringRange(v_docComment_1432_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v_body_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
lean_dec_ref_known(v___x_1440_, 1);
v___x_1441_ = lean_unsigned_to_nat(1u);
v_body_1442_ = l_Lean_Syntax_getArg(v_docComment_1432_, v___x_1441_);
v___x_1443_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1444_ = l_Lean_Syntax_isOfKind(v_body_1442_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = l_Lean_TSyntax_getDocString(v_docComment_1432_);
v___x_1446_ = l_Lean_versoDocStringOfText(v_declName_1430_, v_binders_1431_, v___x_1445_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; lean_object* v_markup_1448_; 
v___x_1447_ = l_Lean_VersoDocstringView_of(v_docComment_1432_);
v_markup_1448_ = lean_ctor_get(v___x_1447_, 1);
lean_inc_ref(v_markup_1448_);
lean_dec_ref(v___x_1447_);
if (lean_obj_tag(v_markup_1448_) == 0)
{
lean_object* v_doc_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_doc_1449_ = lean_ctor_get(v_markup_1448_, 0);
lean_inc(v_doc_1449_);
lean_dec_ref_known(v_markup_1448_, 1);
v___x_1450_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1449_);
lean_dec(v_doc_1449_);
v___x_1451_ = lean_box(0);
v___x_1452_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1430_, v_binders_1431_, v___x_1450_, v___x_1451_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1452_;
}
else
{
lean_object* v_text_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_text_1453_ = lean_ctor_get(v_markup_1448_, 0);
lean_inc(v_text_1453_);
lean_dec_ref_known(v_markup_1448_, 1);
v___x_1454_ = l_Lean_Syntax_getAtomVal(v_text_1453_);
lean_dec(v_text_1453_);
v___x_1455_ = l_Lean_versoDocStringOfText(v_declName_1430_, v_binders_1431_, v___x_1454_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
return v___x_1455_;
}
}
}
else
{
lean_object* v___x_1456_; 
lean_dec_ref_known(v___x_1440_, 1);
v___x_1456_ = l_Lean_parseVersoDocString(v_docComment_1432_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1504_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1504_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1504_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
if (lean_obj_tag(v_a_1457_) == 1)
{
lean_object* v_val_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; 
lean_del_object(v___x_1459_);
v_val_1461_ = lean_ctor_get(v_a_1457_, 0);
lean_inc(v_val_1461_);
lean_dec_ref_known(v_a_1457_, 1);
v___x_1462_ = l_Lean_TSyntax_getVersoBlocks(v_val_1461_);
lean_dec(v_val_1461_);
v___x_1463_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1463_, 0, v___x_1462_);
v___x_1464_ = 0;
v___x_1465_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1430_, v_binders_1431_, v___x_1463_, v___x_1464_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1491_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1491_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1491_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_fst_1470_; lean_object* v_snd_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1490_; 
v_fst_1470_ = lean_ctor_get(v_a_1466_, 0);
v_snd_1471_ = lean_ctor_get(v_a_1466_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_a_1466_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1473_ = v_a_1466_;
v_isShared_1474_ = v_isSharedCheck_1490_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snd_1471_);
lean_inc(v_fst_1470_);
lean_dec(v_a_1466_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1490_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1489_; 
v_fst_1475_ = lean_ctor_get(v_fst_1470_, 0);
v_snd_1476_ = lean_ctor_get(v_fst_1470_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_fst_1470_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1478_ = v_fst_1470_;
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_snd_1476_);
lean_inc(v_fst_1475_);
lean_dec(v_fst_1470_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_fst_1475_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_snd_1476_);
v___x_1481_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1481_);
v___x_1483_ = v___x_1473_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_snd_1471_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1483_);
v___x_1485_ = v___x_1468_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1465_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1465_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_dec(v_a_1457_);
lean_dec(v_binders_1431_);
lean_dec(v_declName_1430_);
v___x_1500_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1500_);
v___x_1502_ = v___x_1459_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_binders_1431_);
lean_dec(v_declName_1430_);
v_a_1505_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1456_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1456_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1513_, lean_object* v_binders_1514_, lean_object* v_docComment_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_versoDocString(v_declName_1513_, v_binders_1514_, v_docComment_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_docComment_1515_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1524_, lean_object* v_doc_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v_env_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1533_ = lean_st_ref_get(v_a_1531_);
v_env_1540_ = lean_ctor_get(v___x_1533_, 0);
lean_inc_ref(v_env_1540_);
lean_dec(v___x_1533_);
v___x_1541_ = l_Lean_getMainVersoModuleDocs(v_env_1540_);
v___x_1542_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1541_);
lean_dec_ref(v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1543_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1525_);
v___x_1544_ = lean_unsigned_to_nat(0u);
v___y_1535_ = v___x_1543_;
v___y_1536_ = v___x_1544_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v_val_1545_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1546_ = lean_unsigned_to_nat(1u);
v___x_1547_ = lean_nat_add(v_val_1545_, v___x_1546_);
lean_dec(v_val_1545_);
v___x_1548_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1525_);
v___y_1535_ = v___x_1548_;
v___y_1536_ = v___x_1547_;
goto v___jp_1534_;
}
v___jp_1534_:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1537_, 0, v_range_1524_);
lean_closure_set(v___x_1537_, 1, v___y_1535_);
lean_closure_set(v___x_1537_, 2, v___y_1536_);
v___x_1538_ = 0;
v___x_1539_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1537_, v___x_1538_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1549_, lean_object* v_doc_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_versoModDocString(v_range_1549_, v_doc_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_doc_1550_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1568_, lean_object* v_docComment_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1578_ = l_Lean_versoDocStringOfText(v_declName_1568_, v___x_1577_, v_docComment_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1579_, lean_object* v_docComment_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Lean_versoDocStringFromString(v_declName_1579_, v_docComment_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1589_, lean_object* v_declName_1590_, uint8_t v___x_1591_, lean_object* v_env_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_docStringExt;
v___x_1594_ = l_String_removeLeadingSpaces(v_docString_1589_);
v___x_1595_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1593_, v_env_1592_, v_declName_1590_, v___x_1594_, v___x_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object* v_docString_1596_, lean_object* v_declName_1597_, lean_object* v___x_1598_, lean_object* v_env_1599_){
_start:
{
uint8_t v___x_198__boxed_1600_; lean_object* v_res_1601_; 
v___x_198__boxed_1600_ = lean_unbox(v___x_1598_);
v_res_1601_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1596_, v_declName_1597_, v___x_198__boxed_1600_, v_env_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1602_, uint8_t v___x_1603_, lean_object* v_modifyEnv_1604_, lean_object* v_docString_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v___x_1606_ = lean_box(v___x_1603_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1607_, 0, v_docString_1605_);
lean_closure_set(v___f_1607_, 1, v_declName_1602_);
lean_closure_set(v___f_1607_, 2, v___x_1606_);
v___x_1608_ = lean_apply_1(v_modifyEnv_1604_, v___f_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object* v_declName_1609_, lean_object* v___x_1610_, lean_object* v_modifyEnv_1611_, lean_object* v_docString_1612_){
_start:
{
uint8_t v___x_207__boxed_1613_; lean_object* v_res_1614_; 
v___x_207__boxed_1613_ = lean_unbox(v___x_1610_);
v_res_1614_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1609_, v___x_207__boxed_1613_, v_modifyEnv_1611_, v_docString_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_docComment_1617_, lean_object* v_toBind_1618_, lean_object* v___f_1619_, lean_object* v_____r_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = l_Lean_getDocStringText___redArg(v_inst_1615_, v_inst_1616_, v_docComment_1617_);
v___x_1622_ = lean_apply_4(v_toBind_1618_, lean_box(0), lean_box(0), v___x_1621_, v___f_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_docComment_1628_, lean_object* v_toBind_1629_, lean_object* v___f_1630_, lean_object* v_____r_1631_){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = l_Lean_validateDocComment___redArg(v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_docComment_1628_);
v___x_1633_ = lean_apply_4(v_toBind_1629_, lean_box(0), lean_box(0), v___x_1632_, v___f_1630_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1634_, lean_object* v_inst_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_docComment_1639_, lean_object* v_toBind_1640_, lean_object* v___f_1641_, lean_object* v_____r_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1634_, v_inst_1635_, v_inst_1636_, v_inst_1637_, v_inst_1638_, v_docComment_1639_, v_toBind_1640_, v___f_1641_, v_____r_1642_);
lean_dec(v_docComment_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1644_, lean_object* v_____r_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_apply_1(v___f_1644_, v_____r_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v_declName_1653_, lean_object* v___f_1654_, uint8_t v___x_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_toBind_1658_, lean_object* v___f_1659_, lean_object* v_____do__lift_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1660_, v_declName_1653_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_dec(v___f_1659_);
lean_dec(v_toBind_1658_);
lean_dec_ref(v_inst_1657_);
lean_dec_ref(v_inst_1656_);
lean_dec(v_declName_1653_);
v___x_1662_ = lean_box(0);
v___x_1663_ = lean_apply_1(v___f_1654_, v___x_1662_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref_known(v___x_1661_, 1);
lean_dec(v___f_1654_);
v___x_1664_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1665_ = l_Lean_MessageData_ofConstName(v_declName_1653_, v___x_1655_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_throwError___redArg(v_inst_1656_, v_inst_1657_, v___x_1668_);
v___x_1670_ = lean_apply_4(v_toBind_1658_, lean_box(0), lean_box(0), v___x_1669_, v___f_1659_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v_declName_1671_, lean_object* v___f_1672_, lean_object* v___x_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_toBind_1676_, lean_object* v___f_1677_, lean_object* v_____do__lift_1678_){
_start:
{
uint8_t v___x_272__boxed_1679_; lean_object* v_res_1680_; 
v___x_272__boxed_1679_ = lean_unbox(v___x_1673_);
v_res_1680_ = l_Lean_addMarkdownDocString___redArg___lam__5(v_declName_1671_, v___f_1672_, v___x_272__boxed_1679_, v_inst_1674_, v_inst_1675_, v_toBind_1676_, v___f_1677_, v_____do__lift_1678_);
lean_dec_ref(v_____do__lift_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_inst_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_, lean_object* v_inst_1687_, lean_object* v_declName_1688_, lean_object* v_docComment_1689_){
_start:
{
lean_object* v_toApplicative_1690_; lean_object* v_toBind_1691_; lean_object* v_toPure_1692_; uint8_t v___x_1693_; 
v_toApplicative_1690_ = lean_ctor_get(v_inst_1681_, 0);
v_toBind_1691_ = lean_ctor_get(v_inst_1681_, 1);
lean_inc(v_toBind_1691_);
v_toPure_1692_ = lean_ctor_get(v_toApplicative_1690_, 1);
v___x_1693_ = l_Lean_Name_isAnonymous(v_declName_1688_);
if (v___x_1693_ == 0)
{
lean_object* v_getEnv_1694_; lean_object* v_modifyEnv_1695_; uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; 
v_getEnv_1694_ = lean_ctor_get(v_inst_1684_, 0);
lean_inc(v_getEnv_1694_);
v_modifyEnv_1695_ = lean_ctor_get(v_inst_1684_, 1);
lean_inc(v_modifyEnv_1695_);
lean_dec_ref(v_inst_1684_);
v___x_1696_ = 1;
v___x_1697_ = lean_box(v___x_1696_);
lean_inc(v_declName_1688_);
v___f_1698_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1698_, 0, v_declName_1688_);
lean_closure_set(v___f_1698_, 1, v___x_1697_);
lean_closure_set(v___f_1698_, 2, v_modifyEnv_1695_);
lean_inc_n(v_toBind_1691_, 3);
lean_inc(v_docComment_1689_);
lean_inc_ref(v_inst_1685_);
lean_inc_ref_n(v_inst_1681_, 2);
v___f_1699_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1699_, 0, v_inst_1681_);
lean_closure_set(v___f_1699_, 1, v_inst_1685_);
lean_closure_set(v___f_1699_, 2, v_docComment_1689_);
lean_closure_set(v___f_1699_, 3, v_toBind_1691_);
lean_closure_set(v___f_1699_, 4, v___f_1698_);
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1700_, 0, v_inst_1681_);
lean_closure_set(v___f_1700_, 1, v_inst_1682_);
lean_closure_set(v___f_1700_, 2, v_inst_1686_);
lean_closure_set(v___f_1700_, 3, v_inst_1687_);
lean_closure_set(v___f_1700_, 4, v_inst_1683_);
lean_closure_set(v___f_1700_, 5, v_docComment_1689_);
lean_closure_set(v___f_1700_, 6, v_toBind_1691_);
lean_closure_set(v___f_1700_, 7, v___f_1699_);
lean_inc_ref(v___f_1700_);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1701_, 0, v___f_1700_);
v___x_1702_ = lean_box(v___x_1693_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1703_, 0, v_declName_1688_);
lean_closure_set(v___f_1703_, 1, v___f_1700_);
lean_closure_set(v___f_1703_, 2, v___x_1702_);
lean_closure_set(v___f_1703_, 3, v_inst_1681_);
lean_closure_set(v___f_1703_, 4, v_inst_1685_);
lean_closure_set(v___f_1703_, 5, v_toBind_1691_);
lean_closure_set(v___f_1703_, 6, v___f_1701_);
v___x_1704_ = lean_apply_4(v_toBind_1691_, lean_box(0), lean_box(0), v_getEnv_1694_, v___f_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_inc(v_toPure_1692_);
lean_dec(v_toBind_1691_);
lean_dec(v_docComment_1689_);
lean_dec(v_declName_1688_);
lean_dec(v_inst_1687_);
lean_dec_ref(v_inst_1686_);
lean_dec_ref(v_inst_1685_);
lean_dec_ref(v_inst_1684_);
lean_dec_ref(v_inst_1683_);
lean_dec(v_inst_1682_);
lean_dec_ref(v_inst_1681_);
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_apply_2(v_toPure_1692_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_declName_1715_, lean_object* v_docComment_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Lean_addMarkdownDocString___redArg(v_inst_1708_, v_inst_1709_, v_inst_1710_, v_inst_1711_, v_inst_1712_, v_inst_1713_, v_inst_1714_, v_declName_1715_, v_docComment_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v_addEntryFn_1718_, lean_object* v___x_1719_, lean_object* v_s_1720_){
_start:
{
lean_object* v_importedEntries_1721_; lean_object* v_state_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1730_; 
v_importedEntries_1721_ = lean_ctor_get(v_s_1720_, 0);
v_state_1722_ = lean_ctor_get(v_s_1720_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_s_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1724_ = v_s_1720_;
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_state_1722_);
lean_inc(v_importedEntries_1721_);
lean_dec(v_s_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1730_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_state_1726_; lean_object* v___x_1728_; 
v_state_1726_ = lean_apply_2(v_addEntryFn_1718_, v_state_1722_, v___x_1719_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_state_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_importedEntries_1721_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_state_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1731_, lean_object* v_x1_1732_, lean_object* v_x2_1733_){
_start:
{
lean_object* v_index_1734_; lean_object* v_sourceString_1735_; lean_object* v_imports_1736_; lean_object* v_currNamespace_1737_; lean_object* v_openDecls_1738_; lean_object* v_options_1739_; lean_object* v_check_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1759_; 
v_index_1734_ = lean_ctor_get(v_x2_1733_, 1);
v_sourceString_1735_ = lean_ctor_get(v_x2_1733_, 2);
v_imports_1736_ = lean_ctor_get(v_x2_1733_, 3);
v_currNamespace_1737_ = lean_ctor_get(v_x2_1733_, 4);
v_openDecls_1738_ = lean_ctor_get(v_x2_1733_, 5);
v_options_1739_ = lean_ctor_get(v_x2_1733_, 6);
v_check_1740_ = lean_ctor_get(v_x2_1733_, 7);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_x2_1733_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v_x2_1733_, 0);
lean_dec(v_unused_1760_);
v___x_1742_ = v_x2_1733_;
v_isShared_1743_ = v_isSharedCheck_1759_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_check_1740_);
lean_inc(v_options_1739_);
lean_inc(v_openDecls_1738_);
lean_inc(v_currNamespace_1737_);
lean_inc(v_imports_1736_);
lean_inc(v_sourceString_1735_);
lean_inc(v_index_1734_);
lean_dec(v_x2_1733_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1759_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v_toEnvExtension_1745_; lean_object* v_addEntryFn_1746_; lean_object* v_asyncMode_1747_; uint8_t v_logWrites_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1744_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1745_ = lean_ctor_get(v___x_1744_, 0);
v_addEntryFn_1746_ = lean_ctor_get(v___x_1744_, 3);
v_asyncMode_1747_ = lean_ctor_get(v_toEnvExtension_1745_, 2);
v_logWrites_1748_ = lean_ctor_get_uint8(v_toEnvExtension_1745_, sizeof(void*)*6);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v_declName_1731_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1749_);
v___x_1751_ = v___x_1742_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_index_1734_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_sourceString_1735_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_imports_1736_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_currNamespace_1737_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v_openDecls_1738_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v_options_1739_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_check_1740_);
v___x_1751_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___f_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
lean_inc(v_addEntryFn_1746_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1752_, 0, v_addEntryFn_1746_);
lean_closure_set(v___f_1752_, 1, v___x_1751_);
v___x_1753_ = lean_box(0);
v___x_1754_ = 1;
if (v_logWrites_1748_ == 0)
{
lean_object* v___x_1755_; 
lean_inc_ref(v_toEnvExtension_1745_);
v___x_1755_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1745_, v_x1_1732_, v___f_1752_, v_asyncMode_1747_, v___x_1753_, v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_inc_ref_n(v_toEnvExtension_1745_, 2);
v___x_1756_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1745_, v_x1_1732_);
lean_dec_ref(v_x1_1732_);
v___x_1757_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1745_, v___x_1756_, v___f_1752_, v_asyncMode_1747_, v___x_1753_, v___x_1754_);
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_1780_, lean_object* v_docs_1781_, uint8_t v___x_1782_, lean_object* v_deferred_1783_, lean_object* v___f_1784_, lean_object* v_env_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v_env_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1786_ = l_Lean_versoDocStringExt;
v_env_1787_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1786_, v_env_1785_, v_declName_1780_, v_docs_1781_, v___x_1782_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_array_get_size(v_deferred_1783_);
v___x_1790_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1791_ = lean_nat_dec_lt(v___x_1788_, v___x_1789_);
if (v___x_1791_ == 0)
{
lean_dec_ref(v___f_1784_);
lean_dec_ref(v_deferred_1783_);
return v_env_1787_;
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((size_t)0ULL);
v___x_1793_ = lean_usize_of_nat(v___x_1789_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1790_, v___f_1784_, v_deferred_1783_, v___x_1792_, v___x_1793_, v_env_1787_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1795_, lean_object* v_docs_1796_, lean_object* v___x_1797_, lean_object* v_deferred_1798_, lean_object* v___f_1799_, lean_object* v_env_1800_){
_start:
{
uint8_t v___x_385__boxed_1801_; lean_object* v_res_1802_; 
v___x_385__boxed_1801_ = lean_unbox(v___x_1797_);
v_res_1802_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1795_, v_docs_1796_, v___x_385__boxed_1801_, v_deferred_1798_, v___f_1799_, v_env_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_modifyEnv_1803_, lean_object* v___f_1804_, lean_object* v_____r_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_apply_1(v_modifyEnv_1803_, v___f_1804_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object* v_declName_1809_, lean_object* v_modifyEnv_1810_, lean_object* v___f_1811_, uint8_t v___x_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_toBind_1815_, lean_object* v___f_1816_, lean_object* v_____do__lift_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1817_, v_declName_1809_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; 
lean_dec(v___f_1816_);
lean_dec(v_toBind_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec(v_declName_1809_);
v___x_1819_ = lean_apply_1(v_modifyEnv_1810_, v___f_1811_);
return v___x_1819_;
}
else
{
lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v___f_1811_);
lean_dec(v_modifyEnv_1810_);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1835_);
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
else
{
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1823_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_1824_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1809_, v___x_1812_);
v___x_1825_ = lean_string_append(v___x_1823_, v___x_1824_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_1827_ = lean_string_append(v___x_1825_, v___x_1826_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 3);
lean_ctor_set(v___x_1821_, 0, v___x_1827_);
v___x_1829_ = v___x_1821_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
v___x_1831_ = l_Lean_throwError___redArg(v_inst_1813_, v_inst_1814_, v___x_1830_);
v___x_1832_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v___x_1831_, v___f_1816_);
return v___x_1832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object* v_declName_1836_, lean_object* v_modifyEnv_1837_, lean_object* v___f_1838_, lean_object* v___x_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_toBind_1842_, lean_object* v___f_1843_, lean_object* v_____do__lift_1844_){
_start:
{
uint8_t v___x_437__boxed_1845_; lean_object* v_res_1846_; 
v___x_437__boxed_1845_ = lean_unbox(v___x_1839_);
v_res_1846_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1836_, v_modifyEnv_1837_, v___f_1838_, v___x_437__boxed_1845_, v_inst_1840_, v_inst_1841_, v_toBind_1842_, v___f_1843_, v_____do__lift_1844_);
lean_dec_ref(v_____do__lift_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_declName_1850_, lean_object* v_docs_1851_, lean_object* v_deferred_1852_){
_start:
{
lean_object* v_toApplicative_1853_; lean_object* v_toBind_1854_; lean_object* v_toPure_1855_; uint8_t v___x_1856_; 
v_toApplicative_1853_ = lean_ctor_get(v_inst_1847_, 0);
v_toBind_1854_ = lean_ctor_get(v_inst_1847_, 1);
lean_inc(v_toBind_1854_);
v_toPure_1855_ = lean_ctor_get(v_toApplicative_1853_, 1);
v___x_1856_ = l_Lean_Name_isAnonymous(v_declName_1850_);
if (v___x_1856_ == 0)
{
lean_object* v_getEnv_1857_; lean_object* v_modifyEnv_1858_; lean_object* v___f_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___x_1866_; 
v_getEnv_1857_ = lean_ctor_get(v_inst_1848_, 0);
lean_inc(v_getEnv_1857_);
v_modifyEnv_1858_ = lean_ctor_get(v_inst_1848_, 1);
lean_inc_n(v_modifyEnv_1858_, 2);
lean_dec_ref(v_inst_1848_);
lean_inc_n(v_declName_1850_, 2);
v___f_1859_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1859_, 0, v_declName_1850_);
v___x_1860_ = 1;
v___x_1861_ = lean_box(v___x_1860_);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1862_, 0, v_declName_1850_);
lean_closure_set(v___f_1862_, 1, v_docs_1851_);
lean_closure_set(v___f_1862_, 2, v___x_1861_);
lean_closure_set(v___f_1862_, 3, v_deferred_1852_);
lean_closure_set(v___f_1862_, 4, v___f_1859_);
lean_inc_ref(v___f_1862_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1863_, 0, v_modifyEnv_1858_);
lean_closure_set(v___f_1863_, 1, v___f_1862_);
v___x_1864_ = lean_box(v___x_1860_);
lean_inc(v_toBind_1854_);
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_1865_, 0, v_declName_1850_);
lean_closure_set(v___f_1865_, 1, v_modifyEnv_1858_);
lean_closure_set(v___f_1865_, 2, v___f_1862_);
lean_closure_set(v___f_1865_, 3, v___x_1864_);
lean_closure_set(v___f_1865_, 4, v_inst_1847_);
lean_closure_set(v___f_1865_, 5, v_inst_1849_);
lean_closure_set(v___f_1865_, 6, v_toBind_1854_);
lean_closure_set(v___f_1865_, 7, v___f_1863_);
v___x_1866_ = lean_apply_4(v_toBind_1854_, lean_box(0), lean_box(0), v_getEnv_1857_, v___f_1865_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_inc(v_toPure_1855_);
lean_dec(v_toBind_1854_);
lean_dec_ref(v_deferred_1852_);
lean_dec_ref(v_docs_1851_);
lean_dec(v_declName_1850_);
lean_dec_ref(v_inst_1849_);
lean_dec_ref(v_inst_1848_);
lean_dec_ref(v_inst_1847_);
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_apply_2(v_toPure_1855_, lean_box(0), v___x_1867_);
return v___x_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_declName_1874_, lean_object* v_docs_1875_, lean_object* v_deferred_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1870_, v_inst_1871_, v_inst_1873_, v_declName_1874_, v_docs_1875_, v_deferred_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1878_, lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_declName_1883_, lean_object* v_docs_1884_, lean_object* v_deferred_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_addVersoDocStringCore(v_m_1878_, v_inst_1879_, v_inst_1880_, v_inst_1881_, v_inst_1882_, v_declName_1883_, v_docs_1884_, v_deferred_1885_);
lean_dec(v_inst_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_size_1887_, uint8_t v___x_1888_, lean_object* v_x1_1889_, lean_object* v_x2_1890_){
_start:
{
lean_object* v_index_1891_; lean_object* v_sourceString_1892_; lean_object* v_imports_1893_; lean_object* v_currNamespace_1894_; lean_object* v_openDecls_1895_; lean_object* v_options_1896_; lean_object* v_check_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1915_; 
v_index_1891_ = lean_ctor_get(v_x2_1890_, 1);
v_sourceString_1892_ = lean_ctor_get(v_x2_1890_, 2);
v_imports_1893_ = lean_ctor_get(v_x2_1890_, 3);
v_currNamespace_1894_ = lean_ctor_get(v_x2_1890_, 4);
v_openDecls_1895_ = lean_ctor_get(v_x2_1890_, 5);
v_options_1896_ = lean_ctor_get(v_x2_1890_, 6);
v_check_1897_ = lean_ctor_get(v_x2_1890_, 7);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x2_1890_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_x2_1890_, 0);
lean_dec(v_unused_1916_);
v___x_1899_ = v_x2_1890_;
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_check_1897_);
lean_inc(v_options_1896_);
lean_inc(v_openDecls_1895_);
lean_inc(v_currNamespace_1894_);
lean_inc(v_imports_1893_);
lean_inc(v_sourceString_1892_);
lean_inc(v_index_1891_);
lean_dec(v_x2_1890_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v_toEnvExtension_1902_; lean_object* v_addEntryFn_1903_; lean_object* v_asyncMode_1904_; uint8_t v_logWrites_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1901_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1902_ = lean_ctor_get(v___x_1901_, 0);
v_addEntryFn_1903_ = lean_ctor_get(v___x_1901_, 3);
v_asyncMode_1904_ = lean_ctor_get(v_toEnvExtension_1902_, 2);
v_logWrites_1905_ = lean_ctor_get_uint8(v_toEnvExtension_1902_, sizeof(void*)*6);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v_size_1887_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1906_);
v___x_1908_ = v___x_1899_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_index_1891_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_sourceString_1892_);
lean_ctor_set(v_reuseFailAlloc_1914_, 3, v_imports_1893_);
lean_ctor_set(v_reuseFailAlloc_1914_, 4, v_currNamespace_1894_);
lean_ctor_set(v_reuseFailAlloc_1914_, 5, v_openDecls_1895_);
lean_ctor_set(v_reuseFailAlloc_1914_, 6, v_options_1896_);
lean_ctor_set(v_reuseFailAlloc_1914_, 7, v_check_1897_);
v___x_1908_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; 
lean_inc(v_addEntryFn_1903_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1909_, 0, v_addEntryFn_1903_);
lean_closure_set(v___f_1909_, 1, v___x_1908_);
v___x_1910_ = lean_box(0);
if (v_logWrites_1905_ == 0)
{
lean_object* v___x_1911_; 
lean_inc_ref(v_toEnvExtension_1902_);
v___x_1911_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1902_, v_x1_1889_, v___f_1909_, v_asyncMode_1904_, v___x_1910_, v___x_1888_);
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_inc_ref_n(v_toEnvExtension_1902_, 2);
v___x_1912_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1902_, v_x1_1889_);
lean_dec_ref(v_x1_1889_);
v___x_1913_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1902_, v___x_1912_, v___f_1909_, v_asyncMode_1904_, v___x_1910_, v___x_1888_);
return v___x_1913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object* v_size_1917_, lean_object* v___x_1918_, lean_object* v_x1_1919_, lean_object* v_x2_1920_){
_start:
{
uint8_t v___x_305__boxed_1921_; lean_object* v_res_1922_; 
v___x_305__boxed_1921_ = lean_unbox(v___x_1918_);
v_res_1922_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1917_, v___x_305__boxed_1921_, v_x1_1919_, v_x2_1920_);
return v_res_1922_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_1926_, lean_object* v_inst_1927_, lean_object* v_inst_1928_, lean_object* v_deferred_1929_, lean_object* v_inst_1930_, lean_object* v___f_1931_, lean_object* v_____do__lift_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1932_, v_docs_1926_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
lean_dec_ref(v___f_1931_);
lean_dec_ref(v_inst_1930_);
lean_dec_ref(v_deferred_1929_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_1936_ = l_Lean_stringToMessageData(v_a_1934_);
v___x_1937_ = l_Lean_indentD(v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Lean_throwError___redArg(v_inst_1927_, v_inst_1928_, v___x_1938_);
return v___x_1939_;
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
lean_dec_ref(v_inst_1928_);
lean_dec_ref(v_inst_1927_);
v_a_1940_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_array_get_size(v_deferred_1929_);
v___x_1943_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1944_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v___f_1931_);
lean_dec_ref(v_deferred_1929_);
v___x_1945_ = l_Lean_setEnv___redArg(v_inst_1930_, v_a_1940_);
return v___x_1945_;
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = lean_usize_of_nat(v___x_1942_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1943_, v___f_1931_, v_deferred_1929_, v___x_1946_, v___x_1947_, v_a_1940_);
v___x_1949_ = l_Lean_setEnv___redArg(v_inst_1930_, v___x_1948_);
return v___x_1949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t v___x_1950_, lean_object* v_docs_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_deferred_1954_, lean_object* v_inst_1955_, lean_object* v_toBind_1956_, lean_object* v_getEnv_1957_, lean_object* v_____do__lift_1958_){
_start:
{
lean_object* v___x_1959_; lean_object* v_size_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___x_1964_; 
v___x_1959_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1958_);
v_size_1960_ = lean_ctor_get(v___x_1959_, 2);
lean_inc(v_size_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = lean_box(v___x_1950_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1962_, 0, v_size_1960_);
lean_closure_set(v___f_1962_, 1, v___x_1961_);
v___f_1963_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1963_, 0, v_docs_1951_);
lean_closure_set(v___f_1963_, 1, v_inst_1952_);
lean_closure_set(v___f_1963_, 2, v_inst_1953_);
lean_closure_set(v___f_1963_, 3, v_deferred_1954_);
lean_closure_set(v___f_1963_, 4, v_inst_1955_);
lean_closure_set(v___f_1963_, 5, v___f_1962_);
v___x_1964_ = lean_apply_4(v_toBind_1956_, lean_box(0), lean_box(0), v_getEnv_1957_, v___f_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object* v___x_1965_, lean_object* v_docs_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_deferred_1969_, lean_object* v_inst_1970_, lean_object* v_toBind_1971_, lean_object* v_getEnv_1972_, lean_object* v_____do__lift_1973_){
_start:
{
uint8_t v___x_416__boxed_1974_; lean_object* v_res_1975_; 
v___x_416__boxed_1974_ = lean_unbox(v___x_1965_);
v_res_1975_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_416__boxed_1974_, v_docs_1966_, v_inst_1967_, v_inst_1968_, v_deferred_1969_, v_inst_1970_, v_toBind_1971_, v_getEnv_1972_, v_____do__lift_1973_);
return v_res_1975_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_docs_1981_, lean_object* v_deferred_1982_, lean_object* v_inst_1983_, lean_object* v_toBind_1984_, lean_object* v_getEnv_1985_, lean_object* v_____do__lift_1986_){
_start:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = l_Lean_getMainModuleDoc(v_____do__lift_1986_);
v___x_1988_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_1987_);
lean_dec_ref(v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v_getEnv_1985_);
lean_dec(v_toBind_1984_);
lean_dec_ref(v_inst_1983_);
lean_dec_ref(v_deferred_1982_);
lean_dec_ref(v_docs_1981_);
v___x_1989_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_1990_ = l_Lean_throwError___redArg(v_inst_1979_, v_inst_1980_, v___x_1989_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_box(v___x_1988_);
lean_inc(v_getEnv_1985_);
lean_inc(v_toBind_1984_);
v___f_1992_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_1992_, 0, v___x_1991_);
lean_closure_set(v___f_1992_, 1, v_docs_1981_);
lean_closure_set(v___f_1992_, 2, v_inst_1979_);
lean_closure_set(v___f_1992_, 3, v_inst_1980_);
lean_closure_set(v___f_1992_, 4, v_deferred_1982_);
lean_closure_set(v___f_1992_, 5, v_inst_1983_);
lean_closure_set(v___f_1992_, 6, v_toBind_1984_);
lean_closure_set(v___f_1992_, 7, v_getEnv_1985_);
v___x_1993_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v_getEnv_1985_, v___f_1992_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_inst_1996_, lean_object* v_docs_1997_, lean_object* v_deferred_1998_){
_start:
{
lean_object* v_toBind_1999_; lean_object* v_getEnv_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; 
v_toBind_1999_ = lean_ctor_get(v_inst_1994_, 1);
lean_inc_n(v_toBind_1999_, 2);
v_getEnv_2000_ = lean_ctor_get(v_inst_1995_, 0);
lean_inc_n(v_getEnv_2000_, 2);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2001_, 0, v_inst_1994_);
lean_closure_set(v___f_2001_, 1, v_inst_1996_);
lean_closure_set(v___f_2001_, 2, v_docs_1997_);
lean_closure_set(v___f_2001_, 3, v_deferred_1998_);
lean_closure_set(v___f_2001_, 4, v_inst_1995_);
lean_closure_set(v___f_2001_, 5, v_toBind_1999_);
lean_closure_set(v___f_2001_, 6, v_getEnv_2000_);
v___x_2002_ = lean_apply_4(v_toBind_1999_, lean_box(0), lean_box(0), v_getEnv_2000_, v___f_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_inst_2006_, lean_object* v_inst_2007_, lean_object* v_docs_2008_, lean_object* v_deferred_2009_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2004_, v_inst_2005_, v_inst_2007_, v_docs_2008_, v_deferred_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_docs_2016_, lean_object* v_deferred_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_addVersoModDocStringCore(v_m_2011_, v_inst_2012_, v_inst_2013_, v_inst_2014_, v_inst_2015_, v_docs_2016_, v_deferred_2017_);
lean_dec(v_inst_2014_);
return v_res_2018_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(1);
v___x_2020_ = l_Lean_MessageData_ofFormat(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__2));
v___x_2025_ = l_Lean_MessageData_ofFormat(v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5(lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
return v_x_2026_;
}
else
{
lean_object* v_head_2028_; lean_object* v_tail_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2051_; 
v_head_2028_ = lean_ctor_get(v_x_2027_, 0);
v_tail_2029_ = lean_ctor_get(v_x_2027_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2031_ = v_x_2027_;
v_isShared_2032_ = v_isSharedCheck_2051_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_tail_2029_);
lean_inc(v_head_2028_);
lean_dec(v_x_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2051_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_before_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2049_; 
v_before_2033_ = lean_ctor_get(v_head_2028_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_head_2028_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_head_2028_, 1);
lean_dec(v_unused_2050_);
v___x_2035_ = v_head_2028_;
v_isShared_2036_ = v_isSharedCheck_2049_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_before_2033_);
lean_dec(v_head_2028_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2049_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 7);
lean_ctor_set(v___x_2035_, 1, v___x_2037_);
lean_ctor_set(v___x_2035_, 0, v_x_2026_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_x_2026_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__3);
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 7);
lean_ctor_set(v___x_2031_, 1, v___x_2040_);
lean_ctor_set(v___x_2031_, 0, v___x_2039_);
v___x_2042_ = v___x_2031_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2043_ = l_Lean_MessageData_ofSyntax(v_before_2033_);
v___x_2044_ = l_Lean_indentD(v___x_2043_);
v___x_2045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v_x_2026_ = v___x_2045_;
v_x_2027_ = v_tail_2029_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__1));
v___x_2056_ = l_Lean_MessageData_ofFormat(v___x_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(lean_object* v_msgData_2057_, lean_object* v_macroStack_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2061_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2059_);
v___x_2062_ = l_Lean_Elab_pp_macroStack;
v___x_2063_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2061_, v___x_2062_);
lean_dec_ref(v___x_2061_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec(v_macroStack_2058_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_msgData_2057_);
return v___x_2064_;
}
else
{
if (lean_obj_tag(v_macroStack_2058_) == 0)
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_msgData_2057_);
return v___x_2065_;
}
else
{
lean_object* v_head_2066_; lean_object* v_after_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2082_; 
v_head_2066_ = lean_ctor_get(v_macroStack_2058_, 0);
lean_inc(v_head_2066_);
v_after_2067_ = lean_ctor_get(v_head_2066_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_head_2066_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_head_2066_, 0);
lean_dec(v_unused_2083_);
v___x_2069_ = v_head_2066_;
v_isShared_2070_ = v_isSharedCheck_2082_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_after_2067_);
lean_dec(v_head_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2082_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5___closed__0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 7);
lean_ctor_set(v___x_2069_, 1, v___x_2071_);
lean_ctor_set(v___x_2069_, 0, v_msgData_2057_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_msgData_2057_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_msgData_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2074_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___closed__2);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_MessageData_ofSyntax(v_after_2067_);
v___x_2077_ = l_Lean_indentD(v___x_2076_);
v_msgData_2078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2078_, 0, v___x_2075_);
lean_ctor_set(v_msgData_2078_, 1, v___x_2077_);
v___x_2079_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3_spec__5(v_msgData_2078_, v_macroStack_2058_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_2084_, lean_object* v_macroStack_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_msgData_2084_, v_macroStack_2085_, v___y_2086_);
lean_dec_ref(v___y_2086_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_ref_2097_; lean_object* v_macroStack_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_ref_2097_ = lean_ctor_get(v___y_2094_, 2);
v_macroStack_2098_ = lean_ctor_get(v___y_2090_, 1);
v___x_2099_ = l_Lean_Elab_getBetterRef(v_ref_2097_, v_macroStack_2098_);
v___x_2100_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2089_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
lean_inc(v_macroStack_2098_);
v___x_2102_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_a_2101_, v_macroStack_2098_, v___y_2094_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2099_);
lean_ctor_set(v___x_2107_, 1, v_a_2103_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 1);
lean_ctor_set(v___x_2105_, 0, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2120_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___closed__0);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v___dummy_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg();
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0(lean_object* v_addEntryFn_2127_, lean_object* v___x_2128_, lean_object* v_s_2129_){
_start:
{
lean_object* v_importedEntries_2130_; lean_object* v_state_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
v_importedEntries_2130_ = lean_ctor_get(v_s_2129_, 0);
v_state_2131_ = lean_ctor_get(v_s_2129_, 1);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_s_2129_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2133_ = v_s_2129_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_state_2131_);
lean_inc(v_importedEntries_2130_);
lean_dec(v_s_2129_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_state_2135_; lean_object* v___x_2137_; 
v_state_2135_ = lean_apply_2(v_addEntryFn_2127_, v_state_2131_, v___x_2128_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v_state_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_importedEntries_2130_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_state_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(lean_object* v_declName_2140_, lean_object* v_as_2141_, size_t v_i_2142_, size_t v_stop_2143_, lean_object* v_b_2144_){
_start:
{
lean_object* v___y_2146_; uint8_t v___x_2150_; 
v___x_2150_ = lean_usize_dec_eq(v_i_2142_, v_stop_2143_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v_index_2152_; lean_object* v_sourceString_2153_; lean_object* v_imports_2154_; lean_object* v_currNamespace_2155_; lean_object* v_openDecls_2156_; lean_object* v_options_2157_; lean_object* v_check_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2177_; 
v___x_2151_ = lean_array_uget(v_as_2141_, v_i_2142_);
v_index_2152_ = lean_ctor_get(v___x_2151_, 1);
v_sourceString_2153_ = lean_ctor_get(v___x_2151_, 2);
v_imports_2154_ = lean_ctor_get(v___x_2151_, 3);
v_currNamespace_2155_ = lean_ctor_get(v___x_2151_, 4);
v_openDecls_2156_ = lean_ctor_get(v___x_2151_, 5);
v_options_2157_ = lean_ctor_get(v___x_2151_, 6);
v_check_2158_ = lean_ctor_get(v___x_2151_, 7);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2178_);
v___x_2160_ = v___x_2151_;
v_isShared_2161_ = v_isSharedCheck_2177_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_check_2158_);
lean_inc(v_options_2157_);
lean_inc(v_openDecls_2156_);
lean_inc(v_currNamespace_2155_);
lean_inc(v_imports_2154_);
lean_inc(v_sourceString_2153_);
lean_inc(v_index_2152_);
lean_dec(v___x_2151_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2177_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v_toEnvExtension_2163_; lean_object* v_addEntryFn_2164_; lean_object* v_asyncMode_2165_; uint8_t v_logWrites_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2162_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2163_ = lean_ctor_get(v___x_2162_, 0);
v_addEntryFn_2164_ = lean_ctor_get(v___x_2162_, 3);
v_asyncMode_2165_ = lean_ctor_get(v_toEnvExtension_2163_, 2);
v_logWrites_2166_ = lean_ctor_get_uint8(v_toEnvExtension_2163_, sizeof(void*)*6);
lean_inc(v_declName_2140_);
v___x_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_declName_2140_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2167_);
v___x_2169_ = v___x_2160_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_index_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_sourceString_2153_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_imports_2154_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_currNamespace_2155_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_openDecls_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_options_2157_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_check_2158_);
v___x_2169_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___f_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
lean_inc(v_addEntryFn_2164_);
v___f_2170_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_2170_, 0, v_addEntryFn_2164_);
lean_closure_set(v___f_2170_, 1, v___x_2169_);
v___x_2171_ = lean_box(0);
v___x_2172_ = 1;
if (v_logWrites_2166_ == 0)
{
lean_object* v___x_2173_; 
lean_inc_ref(v_toEnvExtension_2163_);
v___x_2173_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2163_, v_b_2144_, v___f_2170_, v_asyncMode_2165_, v___x_2171_, v___x_2172_);
v___y_2146_ = v___x_2173_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_inc_ref_n(v_toEnvExtension_2163_, 2);
v___x_2174_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2163_, v_b_2144_);
lean_dec_ref(v_b_2144_);
v___x_2175_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2163_, v___x_2174_, v___f_2170_, v_asyncMode_2165_, v___x_2171_, v___x_2172_);
v___y_2146_ = v___x_2175_;
goto v___jp_2145_;
}
}
}
}
else
{
lean_dec(v_declName_2140_);
return v_b_2144_;
}
v___jp_2145_:
{
size_t v___x_2147_; size_t v___x_2148_; 
v___x_2147_ = ((size_t)1ULL);
v___x_2148_ = lean_usize_add(v_i_2142_, v___x_2147_);
v_i_2142_ = v___x_2148_;
v_b_2144_ = v___y_2146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___boxed(lean_object* v_declName_2179_, lean_object* v_as_2180_, lean_object* v_i_2181_, lean_object* v_stop_2182_, lean_object* v_b_2183_){
_start:
{
size_t v_i_boxed_2184_; size_t v_stop_boxed_2185_; lean_object* v_res_2186_; 
v_i_boxed_2184_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_stop_boxed_2185_ = lean_unbox_usize(v_stop_2182_);
lean_dec(v_stop_2182_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(v_declName_2179_, v_as_2180_, v_i_boxed_2184_, v_stop_boxed_2185_, v_b_2183_);
lean_dec_ref(v_as_2180_);
return v_res_2186_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1___redArg();
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
lean_ctor_set(v___x_2196_, 2, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2197_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__4);
v___x_2198_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__3);
v___x_2199_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2200_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
v___x_2201_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
lean_ctor_set(v___x_2201_, 3, v___x_2199_);
lean_ctor_set(v___x_2201_, 4, v___x_2199_);
lean_ctor_set(v___x_2201_, 5, v___x_2199_);
lean_ctor_set(v___x_2201_, 6, v___x_2199_);
lean_ctor_set(v___x_2201_, 7, v___x_2197_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2202_, lean_object* v_docs_2203_, lean_object* v_deferred_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; uint8_t v___x_2244_; 
v___x_2244_ = l_Lean_Name_isAnonymous(v_declName_2202_);
if (v___x_2244_ == 0)
{
uint8_t v___x_2245_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___x_2267_; lean_object* v_env_2268_; lean_object* v___x_2269_; 
v___x_2245_ = 1;
v___x_2267_ = lean_st_ref_get(v___y_2210_);
v_env_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_env_2268_);
lean_dec(v___x_2267_);
v___x_2269_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2268_, v_declName_2202_);
lean_dec_ref(v_env_2268_);
if (lean_obj_tag(v___x_2269_) == 0)
{
v___y_2247_ = v___y_2208_;
v___y_2248_ = v___y_2210_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_docs_2203_);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2283_ == 0)
{
lean_object* v_unused_2284_; 
v_unused_2284_ = lean_ctor_get(v___x_2269_, 0);
lean_dec(v_unused_2284_);
v___x_2271_ = v___x_2269_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_dec(v___x_2269_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2273_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2274_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2202_, v___x_2245_);
v___x_2275_ = lean_string_append(v___x_2273_, v___x_2274_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2277_ = lean_string_append(v___x_2275_, v___x_2276_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 3);
lean_ctor_set(v___x_2271_, 0, v___x_2277_);
v___x_2279_ = v___x_2271_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = l_Lean_MessageData_ofFormat(v___x_2279_);
v___x_2281_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2280_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2281_;
}
}
}
v___jp_2246_:
{
lean_object* v___x_2249_; lean_object* v_env_2250_; lean_object* v_nextMacroScope_2251_; lean_object* v_ngen_2252_; lean_object* v_auxDeclNGen_2253_; lean_object* v_traceState_2254_; lean_object* v_recordedDeps_2255_; lean_object* v_messages_2256_; lean_object* v_infoState_2257_; lean_object* v_snapshotTasks_2258_; lean_object* v___x_2259_; lean_object* v_env_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2249_ = lean_st_ref_take(v___y_2248_);
v_env_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc_ref(v_env_2250_);
v_nextMacroScope_2251_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_nextMacroScope_2251_);
v_ngen_2252_ = lean_ctor_get(v___x_2249_, 2);
lean_inc_ref(v_ngen_2252_);
v_auxDeclNGen_2253_ = lean_ctor_get(v___x_2249_, 3);
lean_inc_ref(v_auxDeclNGen_2253_);
v_traceState_2254_ = lean_ctor_get(v___x_2249_, 4);
lean_inc_ref(v_traceState_2254_);
v_recordedDeps_2255_ = lean_ctor_get(v___x_2249_, 6);
lean_inc_ref(v_recordedDeps_2255_);
v_messages_2256_ = lean_ctor_get(v___x_2249_, 7);
lean_inc_ref(v_messages_2256_);
v_infoState_2257_ = lean_ctor_get(v___x_2249_, 8);
lean_inc_ref(v_infoState_2257_);
v_snapshotTasks_2258_ = lean_ctor_get(v___x_2249_, 9);
lean_inc_ref(v_snapshotTasks_2258_);
lean_dec(v___x_2249_);
v___x_2259_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2202_);
v_env_2260_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2259_, v_env_2250_, v_declName_2202_, v_docs_2203_, v___x_2245_);
v___x_2261_ = lean_unsigned_to_nat(0u);
v___x_2262_ = lean_array_get_size(v_deferred_2204_);
v___x_2263_ = lean_nat_dec_lt(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_dec(v_declName_2202_);
v___y_2213_ = v_ngen_2252_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v_auxDeclNGen_2253_;
v___y_2217_ = v_snapshotTasks_2258_;
v___y_2218_ = v_recordedDeps_2255_;
v___y_2219_ = v_infoState_2257_;
v___y_2220_ = v_traceState_2254_;
v___y_2221_ = v_messages_2256_;
v___y_2222_ = v_nextMacroScope_2251_;
v___y_2223_ = v_env_2260_;
goto v___jp_2212_;
}
else
{
size_t v___x_2264_; size_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = lean_usize_of_nat(v___x_2262_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1(v_declName_2202_, v_deferred_2204_, v___x_2264_, v___x_2265_, v_env_2260_);
v___y_2213_ = v_ngen_2252_;
v___y_2214_ = v___y_2247_;
v___y_2215_ = v___y_2248_;
v___y_2216_ = v_auxDeclNGen_2253_;
v___y_2217_ = v_snapshotTasks_2258_;
v___y_2218_ = v_recordedDeps_2255_;
v___y_2219_ = v_infoState_2257_;
v___y_2220_ = v_traceState_2254_;
v___y_2221_ = v_messages_2256_;
v___y_2222_ = v_nextMacroScope_2251_;
v___y_2223_ = v___x_2266_;
goto v___jp_2212_;
}
}
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec_ref(v_docs_2203_);
lean_dec(v_declName_2202_);
v___x_2285_ = lean_box(0);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
v___jp_2212_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v_mctx_2228_; lean_object* v_zetaDeltaFVarIds_2229_; lean_object* v_postponed_2230_; lean_object* v_diag_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2242_; 
v___x_2224_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2225_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2225_, 0, v___y_2223_);
lean_ctor_set(v___x_2225_, 1, v___y_2222_);
lean_ctor_set(v___x_2225_, 2, v___y_2213_);
lean_ctor_set(v___x_2225_, 3, v___y_2216_);
lean_ctor_set(v___x_2225_, 4, v___y_2220_);
lean_ctor_set(v___x_2225_, 5, v___x_2224_);
lean_ctor_set(v___x_2225_, 6, v___y_2218_);
lean_ctor_set(v___x_2225_, 7, v___y_2221_);
lean_ctor_set(v___x_2225_, 8, v___y_2219_);
lean_ctor_set(v___x_2225_, 9, v___y_2217_);
v___x_2226_ = lean_st_ref_put(v___y_2215_, v___x_2225_);
v___x_2227_ = lean_st_ref_take(v___y_2214_);
v_mctx_2228_ = lean_ctor_get(v___x_2227_, 0);
v_zetaDeltaFVarIds_2229_ = lean_ctor_get(v___x_2227_, 2);
v_postponed_2230_ = lean_ctor_get(v___x_2227_, 3);
v_diag_2231_ = lean_ctor_get(v___x_2227_, 4);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v___x_2227_, 1);
lean_dec(v_unused_2243_);
v___x_2233_ = v___x_2227_;
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_diag_2231_);
lean_inc(v_postponed_2230_);
lean_inc(v_zetaDeltaFVarIds_2229_);
lean_inc(v_mctx_2228_);
lean_dec(v___x_2227_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2242_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v___x_2236_);
v___x_2238_ = v___x_2233_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_mctx_2228_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_zetaDeltaFVarIds_2229_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_postponed_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_diag_2231_);
v___x_2238_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_st_ref_put(v___y_2214_, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2235_);
return v___x_2240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2287_, lean_object* v_docs_2288_, lean_object* v_deferred_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2287_, v_docs_2288_, v_deferred_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_deferred_2289_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2298_, lean_object* v_binders_2299_, lean_object* v_docComment_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___x_2328_; lean_object* v_env_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_st_ref_get(v_a_2306_);
v_env_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_env_2329_);
lean_dec(v___x_2328_);
v___x_2330_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2329_, v_declName_2298_);
lean_dec_ref(v_env_2329_);
if (lean_obj_tag(v___x_2330_) == 0)
{
v___y_2309_ = v_a_2301_;
v___y_2310_ = v_a_2302_;
v___y_2311_ = v_a_2303_;
v___y_2312_ = v_a_2304_;
v___y_2313_ = v_a_2305_;
v___y_2314_ = v_a_2306_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_binders_2299_);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v___x_2330_, 0);
lean_dec(v_unused_2346_);
v___x_2332_ = v___x_2330_;
v_isShared_2333_ = v_isSharedCheck_2345_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v___x_2330_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2345_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2334_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2335_ = 1;
v___x_2336_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2298_, v___x_2335_);
v___x_2337_ = lean_string_append(v___x_2334_, v___x_2336_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2339_ = lean_string_append(v___x_2337_, v___x_2338_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 3);
lean_ctor_set(v___x_2332_, 0, v___x_2339_);
v___x_2341_ = v___x_2332_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = l_Lean_MessageData_ofFormat(v___x_2341_);
v___x_2343_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2342_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2343_;
}
}
}
v___jp_2308_:
{
lean_object* v___x_2315_; 
lean_inc(v_declName_2298_);
v___x_2315_ = l_Lean_versoDocString(v_declName_2298_, v_binders_2299_, v_docComment_2300_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_toVersoDocString_2317_; lean_object* v_deferredChecks_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_toVersoDocString_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc_ref(v_toVersoDocString_2317_);
v_deferredChecks_2318_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_ref(v_deferredChecks_2318_);
lean_dec(v_a_2316_);
v___x_2319_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2298_, v_toVersoDocString_2317_, v_deferredChecks_2318_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec_ref(v_deferredChecks_2318_);
return v___x_2319_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_declName_2298_);
v_a_2320_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2315_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2315_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2347_, lean_object* v_binders_2348_, lean_object* v_docComment_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lean_addVersoDocString(v_declName_2347_, v_binders_2348_, v_docComment_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_docComment_2349_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2368_, lean_object* v_msg_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2368_, v_msg_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___redArg();
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_00_u03b2_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3(lean_object* v_msgData_2386_, lean_object* v_macroStack_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___redArg(v_msgData_2386_, v_macroStack_2387_, v___y_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3___boxed(lean_object* v_msgData_2396_, lean_object* v_macroStack_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__3(v_msgData_2396_, v_macroStack_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2406_, lean_object* v_docComment_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___x_2435_; lean_object* v_env_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_st_ref_get(v_a_2413_);
v_env_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc_ref(v_env_2436_);
lean_dec(v___x_2435_);
v___x_2437_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2436_, v_declName_2406_);
lean_dec_ref(v_env_2436_);
if (lean_obj_tag(v___x_2437_) == 0)
{
v___y_2416_ = v_a_2408_;
v___y_2417_ = v_a_2409_;
v___y_2418_ = v_a_2410_;
v___y_2419_ = v_a_2411_;
v___y_2420_ = v_a_2412_;
v___y_2421_ = v_a_2413_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_docComment_2407_);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2453_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2452_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2452_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2441_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2442_ = 1;
v___x_2443_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2406_, v___x_2442_);
v___x_2444_ = lean_string_append(v___x_2441_, v___x_2443_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2446_ = lean_string_append(v___x_2444_, v___x_2445_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 3);
lean_ctor_set(v___x_2439_, 0, v___x_2446_);
v___x_2448_ = v___x_2439_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = l_Lean_MessageData_ofFormat(v___x_2448_);
v___x_2450_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2449_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
return v___x_2450_;
}
}
}
v___jp_2415_:
{
lean_object* v___x_2422_; 
lean_inc(v_declName_2406_);
v___x_2422_ = l_Lean_versoDocStringFromString(v_declName_2406_, v_docComment_2407_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v_toVersoDocString_2424_; lean_object* v_deferredChecks_2425_; lean_object* v___x_2426_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v_toVersoDocString_2424_ = lean_ctor_get(v_a_2423_, 0);
lean_inc_ref(v_toVersoDocString_2424_);
v_deferredChecks_2425_ = lean_ctor_get(v_a_2423_, 1);
lean_inc_ref(v_deferredChecks_2425_);
lean_dec(v_a_2423_);
v___x_2426_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2406_, v_toVersoDocString_2424_, v_deferredChecks_2425_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec_ref(v_deferredChecks_2425_);
return v___x_2426_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_declName_2406_);
v_a_2427_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2422_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2422_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2454_, lean_object* v_docComment_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_addVersoDocStringFromString(v_declName_2454_, v_docComment_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2464_, lean_object* v_msgData_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = 2;
v___x_2472_ = 0;
v___x_2473_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2464_, v_msgData_2465_, v___x_2471_, v___x_2472_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2474_, lean_object* v_msgData_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2474_, v_msgData_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v_ref_2474_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2482_, lean_object* v_str_2483_, lean_object* v_as_2484_, size_t v_sz_2485_, size_t v_i_2486_, lean_object* v_b_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_a_2496_; uint8_t v___x_2500_; 
v___x_2500_ = lean_usize_dec_lt(v_i_2486_, v_sz_2485_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_b_2487_);
return v___x_2501_;
}
else
{
lean_object* v_a_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v_start_2505_; lean_object* v_stop_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2526_; 
v_a_2502_ = lean_array_uget_borrowed(v_as_2484_, v_i_2486_);
v_fst_2503_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_fst_2503_);
v_snd_2504_ = lean_ctor_get(v_a_2502_, 1);
v_start_2505_ = lean_ctor_get(v_fst_2503_, 0);
v_stop_2506_ = lean_ctor_get(v_fst_2503_, 1);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_fst_2503_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2508_ = v_fst_2503_;
v_isShared_2509_ = v_isSharedCheck_2526_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_stop_2506_);
lean_inc(v_start_2505_);
lean_dec(v_fst_2503_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2526_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_box(0);
if (lean_obj_tag(v___y_2482_) == 1)
{
lean_object* v_val_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v_val_2511_ = lean_ctor_get(v___y_2482_, 0);
v___x_2512_ = lean_nat_add(v_val_2511_, v_start_2505_);
v___x_2513_ = lean_nat_add(v_val_2511_, v_stop_2506_);
v___x_2514_ = 0;
v___x_2515_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2515_, 0, v___x_2512_);
lean_ctor_set(v___x_2515_, 1, v___x_2513_);
lean_ctor_set_uint8(v___x_2515_, sizeof(void*)*2, v___x_2514_);
v___x_2516_ = lean_string_utf8_extract(v_str_2483_, v_start_2505_, v_stop_2506_);
lean_dec(v_stop_2506_);
lean_dec(v_start_2505_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 2);
lean_ctor_set(v___x_2508_, 1, v___x_2516_);
lean_ctor_set(v___x_2508_, 0, v___x_2515_);
v___x_2518_ = v___x_2508_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_inc(v_snd_2504_);
v___x_2519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_snd_2504_);
v___x_2520_ = l_Lean_MessageData_ofFormat(v___x_2519_);
v___x_2521_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2518_, v___x_2520_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec_ref(v___x_2518_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_dec_ref_known(v___x_2521_, 1);
v_a_2496_ = v___x_2510_;
goto v___jp_2495_;
}
else
{
return v___x_2521_;
}
}
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2508_);
lean_dec(v_stop_2506_);
lean_dec(v_start_2505_);
lean_inc(v_snd_2504_);
v___x_2523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2523_, 0, v_snd_2504_);
v___x_2524_ = l_Lean_MessageData_ofFormat(v___x_2523_);
v___x_2525_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2524_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_dec_ref_known(v___x_2525_, 1);
v_a_2496_ = v___x_2510_;
goto v___jp_2495_;
}
else
{
return v___x_2525_;
}
}
}
}
v___jp_2495_:
{
size_t v___x_2497_; size_t v___x_2498_; 
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_add(v_i_2486_, v___x_2497_);
v_i_2486_ = v___x_2498_;
v_b_2487_ = v_a_2496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2527_, lean_object* v_str_2528_, lean_object* v_as_2529_, lean_object* v_sz_2530_, lean_object* v_i_2531_, lean_object* v_b_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
size_t v_sz_boxed_2540_; size_t v_i_boxed_2541_; lean_object* v_res_2542_; 
v_sz_boxed_2540_ = lean_unbox_usize(v_sz_2530_);
lean_dec(v_sz_2530_);
v_i_boxed_2541_ = lean_unbox_usize(v_i_2531_);
lean_dec(v_i_2531_);
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2527_, v_str_2528_, v_as_2529_, v_sz_boxed_2540_, v_i_boxed_2541_, v_b_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v_as_2529_);
lean_dec_ref(v_str_2528_);
lean_dec(v___y_2527_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_str_2551_; lean_object* v___y_2553_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_str_2551_ = l_Lean_TSyntax_getDocString(v_docstring_2543_);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = l_Lean_Syntax_getArg(v_docstring_2543_, v___x_2568_);
v___x_2570_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2569_);
lean_dec(v___x_2569_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_box(0);
v___y_2553_ = v___x_2571_;
goto v___jp_2552_;
}
else
{
lean_object* v_val_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; 
v_val_2572_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2573_ = 0;
v___x_2574_ = l_Lean_SourceInfo_getPos_x3f(v_val_2572_, v___x_2573_);
lean_dec(v_val_2572_);
v___y_2553_ = v___x_2574_;
goto v___jp_2552_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v_fst_2555_; lean_object* v___x_2556_; size_t v_sz_2557_; size_t v___x_2558_; lean_object* v___x_2559_; 
lean_inc_ref(v_str_2551_);
v___x_2554_ = l_Lean_rewriteManualLinksCore(v_str_2551_);
v_fst_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_fst_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = lean_box(0);
v_sz_2557_ = lean_array_size(v_fst_2555_);
v___x_2558_ = ((size_t)0ULL);
v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2553_, v_str_2551_, v_fst_2555_, v_sz_2557_, v___x_2558_, v___x_2556_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v_fst_2555_);
lean_dec_ref(v_str_2551_);
lean_dec(v___y_2553_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2567_);
v___x_2561_ = v___x_2559_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_dec(v___x_2559_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2556_);
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2556_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
return v___x_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v_docstring_2575_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2584_, lean_object* v_msg_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_toCold_2593_; lean_object* v_currRecDepth_2594_; lean_object* v_ref_2595_; uint16_t v_optionFlags_2596_; uint8_t v_suppressElabErrors_2597_; uint8_t v_checkDeprecated_2598_; uint8_t v_isRecordingDeps_2599_; lean_object* v_ref_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_toCold_2593_ = lean_ctor_get(v___y_2590_, 0);
v_currRecDepth_2594_ = lean_ctor_get(v___y_2590_, 1);
v_ref_2595_ = lean_ctor_get(v___y_2590_, 2);
v_optionFlags_2596_ = lean_ctor_get_uint16(v___y_2590_, sizeof(void*)*3);
v_suppressElabErrors_2597_ = lean_ctor_get_uint8(v___y_2590_, sizeof(void*)*3 + 2);
v_checkDeprecated_2598_ = lean_ctor_get_uint8(v___y_2590_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2599_ = lean_ctor_get_uint8(v___y_2590_, sizeof(void*)*3 + 4);
v_ref_2600_ = l_Lean_replaceRef(v_ref_2584_, v_ref_2595_);
lean_inc(v_currRecDepth_2594_);
lean_inc_ref(v_toCold_2593_);
v___x_2601_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2601_, 0, v_toCold_2593_);
lean_ctor_set(v___x_2601_, 1, v_currRecDepth_2594_);
lean_ctor_set(v___x_2601_, 2, v_ref_2600_);
lean_ctor_set_uint16(v___x_2601_, sizeof(void*)*3, v_optionFlags_2596_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 2, v_suppressElabErrors_2597_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 3, v_checkDeprecated_2598_);
lean_ctor_set_uint8(v___x_2601_, sizeof(void*)*3 + 4, v_isRecordingDeps_2599_);
v___x_2602_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___x_2601_, v___y_2591_);
lean_dec_ref_known(v___x_2601_, 3);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v_ref_2603_);
return v_res_2612_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = l_Lean_Syntax_getArg(v_stx_2617_, v___x_2631_);
if (lean_obj_tag(v___x_2632_) == 1)
{
lean_object* v_kind_2633_; 
v_kind_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_kind_2633_);
if (lean_obj_tag(v_kind_2633_) == 1)
{
lean_object* v_pre_2634_; 
v_pre_2634_ = lean_ctor_get(v_kind_2633_, 0);
lean_inc(v_pre_2634_);
if (lean_obj_tag(v_pre_2634_) == 1)
{
lean_object* v_pre_2635_; 
v_pre_2635_ = lean_ctor_get(v_pre_2634_, 0);
lean_inc(v_pre_2635_);
if (lean_obj_tag(v_pre_2635_) == 1)
{
lean_object* v_pre_2636_; 
v_pre_2636_ = lean_ctor_get(v_pre_2635_, 0);
lean_inc(v_pre_2636_);
if (lean_obj_tag(v_pre_2636_) == 1)
{
lean_object* v_pre_2637_; 
v_pre_2637_ = lean_ctor_get(v_pre_2636_, 0);
if (lean_obj_tag(v_pre_2637_) == 0)
{
lean_object* v_args_2638_; lean_object* v_str_2639_; lean_object* v_str_2640_; lean_object* v_str_2641_; lean_object* v_str_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v_args_2638_ = lean_ctor_get(v___x_2632_, 2);
lean_inc_ref(v_args_2638_);
lean_dec_ref_known(v___x_2632_, 3);
v_str_2639_ = lean_ctor_get(v_kind_2633_, 1);
lean_inc_ref(v_str_2639_);
lean_dec_ref_known(v_kind_2633_, 2);
v_str_2640_ = lean_ctor_get(v_pre_2634_, 1);
lean_inc_ref(v_str_2640_);
lean_dec_ref_known(v_pre_2634_, 2);
v_str_2641_ = lean_ctor_get(v_pre_2635_, 1);
lean_inc_ref(v_str_2641_);
lean_dec_ref_known(v_pre_2635_, 2);
v_str_2642_ = lean_ctor_get(v_pre_2636_, 1);
lean_inc_ref(v_str_2642_);
lean_dec_ref_known(v_pre_2636_, 2);
v___x_2643_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2644_ = lean_string_dec_eq(v_str_2642_, v___x_2643_);
lean_dec_ref(v_str_2642_);
if (v___x_2644_ == 0)
{
lean_dec_ref(v_str_2641_);
lean_dec_ref(v_str_2640_);
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_args_2638_);
goto v___jp_2625_;
}
else
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2646_ = lean_string_dec_eq(v_str_2641_, v___x_2645_);
lean_dec_ref(v_str_2641_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v_str_2640_);
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_args_2638_);
goto v___jp_2625_;
}
else
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2648_ = lean_string_dec_eq(v_str_2640_, v___x_2647_);
lean_dec_ref(v_str_2640_);
if (v___x_2648_ == 0)
{
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_args_2638_);
goto v___jp_2625_;
}
else
{
lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2650_ = lean_string_dec_eq(v_str_2639_, v___x_2649_);
lean_dec_ref(v_str_2639_);
if (v___x_2650_ == 0)
{
lean_dec_ref(v_args_2638_);
goto v___jp_2625_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v___x_2651_ = lean_array_get_size(v_args_2638_);
v___x_2652_ = lean_unsigned_to_nat(2u);
v___x_2653_ = lean_nat_dec_eq(v___x_2651_, v___x_2652_);
if (v___x_2653_ == 0)
{
lean_dec_ref(v_args_2638_);
goto v___jp_2625_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_fget(v_args_2638_, v___x_2654_);
lean_dec_ref(v_args_2638_);
if (lean_obj_tag(v___x_2655_) == 2)
{
lean_object* v_val_2656_; lean_object* v___x_2657_; 
lean_dec(v_stx_2617_);
v_val_2656_ = lean_ctor_get(v___x_2655_, 1);
lean_inc_ref(v_val_2656_);
lean_dec_ref_known(v___x_2655_, 2);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_val_2656_);
return v___x_2657_;
}
else
{
lean_dec(v___x_2655_);
goto v___jp_2625_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2636_, 2);
lean_dec_ref_known(v_pre_2635_, 2);
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec_ref_known(v_kind_2633_, 2);
lean_dec_ref_known(v___x_2632_, 3);
goto v___jp_2625_;
}
}
else
{
lean_dec(v_pre_2636_);
lean_dec_ref_known(v_pre_2635_, 2);
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec_ref_known(v_kind_2633_, 2);
lean_dec_ref_known(v___x_2632_, 3);
goto v___jp_2625_;
}
}
else
{
lean_dec(v_pre_2635_);
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec_ref_known(v_kind_2633_, 2);
lean_dec_ref_known(v___x_2632_, 3);
goto v___jp_2625_;
}
}
else
{
lean_dec_ref_known(v_kind_2633_, 2);
lean_dec(v_pre_2634_);
lean_dec_ref_known(v___x_2632_, 3);
goto v___jp_2625_;
}
}
else
{
lean_dec_ref_known(v___x_2632_, 3);
lean_dec(v_kind_2633_);
goto v___jp_2625_;
}
}
else
{
lean_dec(v___x_2632_);
goto v___jp_2625_;
}
v___jp_2625_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2626_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2617_);
v___x_2627_ = l_Lean_MessageData_ofSyntax(v_stx_2617_);
v___x_2628_ = l_Lean_indentD(v___x_2627_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2626_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2617_, v___x_2629_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v_stx_2617_);
return v___x_2630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2667_, lean_object* v_docComment_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_Name_isAnonymous(v_declName_2667_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v___x_2742_; lean_object* v_env_2743_; lean_object* v___x_2744_; 
v___x_2677_ = 1;
v___x_2742_ = lean_st_ref_get(v___y_2674_);
v_env_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc_ref(v_env_2743_);
lean_dec(v___x_2742_);
v___x_2744_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2743_, v_declName_2667_);
lean_dec_ref(v_env_2743_);
if (lean_obj_tag(v___x_2744_) == 0)
{
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
v___y_2683_ = v___y_2673_;
v___y_2684_ = v___y_2674_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec_ref_known(v___x_2744_, 1);
lean_dec(v_docComment_2668_);
v___x_2745_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2746_ = l_Lean_MessageData_ofConstName(v_declName_2667_, v___x_2676_);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2749_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2750_;
}
v___jp_2678_:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2668_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref_known(v___x_2685_, 1);
v___x_2686_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2668_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2733_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2689_ = v___x_2686_;
v_isShared_2690_ = v_isSharedCheck_2733_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2686_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2733_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v_env_2692_; lean_object* v_nextMacroScope_2693_; lean_object* v_ngen_2694_; lean_object* v_auxDeclNGen_2695_; lean_object* v_traceState_2696_; lean_object* v_recordedDeps_2697_; lean_object* v_messages_2698_; lean_object* v_infoState_2699_; lean_object* v_snapshotTasks_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2731_; 
v___x_2691_ = lean_st_ref_take(v___y_2684_);
v_env_2692_ = lean_ctor_get(v___x_2691_, 0);
v_nextMacroScope_2693_ = lean_ctor_get(v___x_2691_, 1);
v_ngen_2694_ = lean_ctor_get(v___x_2691_, 2);
v_auxDeclNGen_2695_ = lean_ctor_get(v___x_2691_, 3);
v_traceState_2696_ = lean_ctor_get(v___x_2691_, 4);
v_recordedDeps_2697_ = lean_ctor_get(v___x_2691_, 6);
v_messages_2698_ = lean_ctor_get(v___x_2691_, 7);
v_infoState_2699_ = lean_ctor_get(v___x_2691_, 8);
v_snapshotTasks_2700_ = lean_ctor_get(v___x_2691_, 9);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2731_ == 0)
{
lean_object* v_unused_2732_; 
v_unused_2732_ = lean_ctor_get(v___x_2691_, 5);
lean_dec(v_unused_2732_);
v___x_2702_ = v___x_2691_;
v_isShared_2703_ = v_isSharedCheck_2731_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_snapshotTasks_2700_);
lean_inc(v_infoState_2699_);
lean_inc(v_messages_2698_);
lean_inc(v_recordedDeps_2697_);
lean_inc(v_traceState_2696_);
lean_inc(v_auxDeclNGen_2695_);
lean_inc(v_ngen_2694_);
lean_inc(v_nextMacroScope_2693_);
lean_inc(v_env_2692_);
lean_dec(v___x_2691_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2731_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2704_ = l_Lean_docStringExt;
v___x_2705_ = l_String_removeLeadingSpaces(v_a_2687_);
v___x_2706_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2704_, v_env_2692_, v_declName_2667_, v___x_2705_, v___x_2677_);
v___x_2707_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 5, v___x_2707_);
lean_ctor_set(v___x_2702_, 0, v___x_2706_);
v___x_2709_ = v___x_2702_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v_nextMacroScope_2693_);
lean_ctor_set(v_reuseFailAlloc_2730_, 2, v_ngen_2694_);
lean_ctor_set(v_reuseFailAlloc_2730_, 3, v_auxDeclNGen_2695_);
lean_ctor_set(v_reuseFailAlloc_2730_, 4, v_traceState_2696_);
lean_ctor_set(v_reuseFailAlloc_2730_, 5, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2730_, 6, v_recordedDeps_2697_);
lean_ctor_set(v_reuseFailAlloc_2730_, 7, v_messages_2698_);
lean_ctor_set(v_reuseFailAlloc_2730_, 8, v_infoState_2699_);
lean_ctor_set(v_reuseFailAlloc_2730_, 9, v_snapshotTasks_2700_);
v___x_2709_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v_mctx_2712_; lean_object* v_zetaDeltaFVarIds_2713_; lean_object* v_postponed_2714_; lean_object* v_diag_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2728_; 
v___x_2710_ = lean_st_ref_put(v___y_2684_, v___x_2709_);
v___x_2711_ = lean_st_ref_take(v___y_2682_);
v_mctx_2712_ = lean_ctor_get(v___x_2711_, 0);
v_zetaDeltaFVarIds_2713_ = lean_ctor_get(v___x_2711_, 2);
v_postponed_2714_ = lean_ctor_get(v___x_2711_, 3);
v_diag_2715_ = lean_ctor_get(v___x_2711_, 4);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2728_ == 0)
{
lean_object* v_unused_2729_; 
v_unused_2729_ = lean_ctor_get(v___x_2711_, 1);
lean_dec(v_unused_2729_);
v___x_2717_ = v___x_2711_;
v_isShared_2718_ = v_isSharedCheck_2728_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_diag_2715_);
lean_inc(v_postponed_2714_);
lean_inc(v_zetaDeltaFVarIds_2713_);
lean_inc(v_mctx_2712_);
lean_dec(v___x_2711_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2728_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
v___x_2719_ = lean_box(0);
v___x_2720_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2720_);
v___x_2722_ = v___x_2717_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_mctx_2712_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_zetaDeltaFVarIds_2713_);
lean_ctor_set(v_reuseFailAlloc_2727_, 3, v_postponed_2714_);
lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_diag_2715_);
v___x_2722_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2723_ = lean_st_ref_put(v___y_2682_, v___x_2722_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2719_);
v___x_2725_ = v___x_2689_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2719_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_declName_2667_);
v_a_2734_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2686_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2686_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_dec(v_docComment_2668_);
lean_dec(v_declName_2667_);
return v___x_2685_;
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec(v_docComment_2668_);
lean_dec(v_declName_2667_);
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2753_, lean_object* v_docComment_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2753_, v_docComment_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2763_, lean_object* v_declName_2764_, lean_object* v_binders_2765_, lean_object* v_docComment_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
if (v_isVerso_2763_ == 0)
{
lean_object* v___x_2774_; 
lean_dec(v_binders_2765_);
v___x_2774_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2764_, v_docComment_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_addVersoDocString(v_declName_2764_, v_binders_2765_, v_docComment_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec(v_docComment_2766_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2776_, lean_object* v_declName_2777_, lean_object* v_binders_2778_, lean_object* v_docComment_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
uint8_t v_isVerso_boxed_2787_; lean_object* v_res_2788_; 
v_isVerso_boxed_2787_ = lean_unbox(v_isVerso_2776_);
v_res_2788_ = l_Lean_addDocStringOf(v_isVerso_boxed_2787_, v_declName_2777_, v_binders_2778_, v_docComment_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2789_, lean_object* v_msgData_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2789_, v_msgData_2790_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2799_, lean_object* v_msgData_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2799_, v_msgData_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v_ref_2799_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2809_, lean_object* v_ref_2810_, lean_object* v_msg_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2810_, v_msg_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_ref_2821_, lean_object* v_msg_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2820_, v_ref_2821_, v_msg_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_ref_2821_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2831_, lean_object* v_t_2832_){
_start:
{
if (lean_obj_tag(v_t_2832_) == 0)
{
lean_object* v_k_2833_; lean_object* v_v_2834_; lean_object* v_l_2835_; lean_object* v_r_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_3490_; 
v_k_2833_ = lean_ctor_get(v_t_2832_, 1);
v_v_2834_ = lean_ctor_get(v_t_2832_, 2);
v_l_2835_ = lean_ctor_get(v_t_2832_, 3);
v_r_2836_ = lean_ctor_get(v_t_2832_, 4);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_t_2832_);
if (v_isSharedCheck_3490_ == 0)
{
lean_object* v_unused_3491_; 
v_unused_3491_ = lean_ctor_get(v_t_2832_, 0);
lean_dec(v_unused_3491_);
v___x_2838_ = v_t_2832_;
v_isShared_2839_ = v_isSharedCheck_3490_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_r_2836_);
lean_inc(v_l_2835_);
lean_inc(v_v_2834_);
lean_inc(v_k_2833_);
lean_dec(v_t_2832_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_3490_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
uint8_t v___x_2840_; 
v___x_2840_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2831_, v_k_2833_);
switch(v___x_2840_)
{
case 0:
{
lean_object* v_impl_2841_; lean_object* v___x_2842_; 
v_impl_2841_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2831_, v_l_2835_);
v___x_2842_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2841_) == 0)
{
if (lean_obj_tag(v_r_2836_) == 0)
{
lean_object* v_size_2843_; lean_object* v_size_2844_; lean_object* v_k_2845_; lean_object* v_v_2846_; lean_object* v_l_2847_; lean_object* v_r_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v_size_2843_ = lean_ctor_get(v_impl_2841_, 0);
v_size_2844_ = lean_ctor_get(v_r_2836_, 0);
v_k_2845_ = lean_ctor_get(v_r_2836_, 1);
v_v_2846_ = lean_ctor_get(v_r_2836_, 2);
v_l_2847_ = lean_ctor_get(v_r_2836_, 3);
lean_inc(v_l_2847_);
v_r_2848_ = lean_ctor_get(v_r_2836_, 4);
v___x_2849_ = lean_unsigned_to_nat(3u);
v___x_2850_ = lean_nat_mul(v___x_2849_, v_size_2843_);
v___x_2851_ = lean_nat_dec_lt(v___x_2850_, v_size_2844_);
lean_dec(v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
lean_dec(v_l_2847_);
v___x_2852_ = lean_nat_add(v___x_2842_, v_size_2843_);
v___x_2853_ = lean_nat_add(v___x_2852_, v_size_2844_);
lean_dec(v___x_2852_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 3, v_impl_2841_);
lean_ctor_set(v___x_2838_, 0, v___x_2853_);
v___x_2855_ = v___x_2838_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_impl_2841_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_r_2836_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2920_; 
lean_inc(v_r_2848_);
lean_inc(v_v_2846_);
lean_inc(v_k_2845_);
lean_inc(v_size_2844_);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2921_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_r_2836_, 2);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_r_2836_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_2925_);
v___x_2858_ = v_r_2836_;
v_isShared_2859_ = v_isSharedCheck_2920_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_r_2836_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2920_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_size_2860_; lean_object* v_k_2861_; lean_object* v_v_2862_; lean_object* v_l_2863_; lean_object* v_r_2864_; lean_object* v_size_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v_size_2860_ = lean_ctor_get(v_l_2847_, 0);
v_k_2861_ = lean_ctor_get(v_l_2847_, 1);
v_v_2862_ = lean_ctor_get(v_l_2847_, 2);
v_l_2863_ = lean_ctor_get(v_l_2847_, 3);
v_r_2864_ = lean_ctor_get(v_l_2847_, 4);
v_size_2865_ = lean_ctor_get(v_r_2848_, 0);
v___x_2866_ = lean_unsigned_to_nat(2u);
v___x_2867_ = lean_nat_mul(v___x_2866_, v_size_2865_);
v___x_2868_ = lean_nat_dec_lt(v_size_2860_, v___x_2867_);
lean_dec(v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2896_; 
lean_inc(v_r_2864_);
lean_inc(v_l_2863_);
lean_inc(v_v_2862_);
lean_inc(v_k_2861_);
v_isSharedCheck_2896_ = !lean_is_exclusive(v_l_2847_);
if (v_isSharedCheck_2896_ == 0)
{
lean_object* v_unused_2897_; lean_object* v_unused_2898_; lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2897_ = lean_ctor_get(v_l_2847_, 4);
lean_dec(v_unused_2897_);
v_unused_2898_ = lean_ctor_get(v_l_2847_, 3);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_l_2847_, 2);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_l_2847_, 1);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_l_2847_, 0);
lean_dec(v_unused_2901_);
v___x_2870_ = v_l_2847_;
v_isShared_2871_ = v_isSharedCheck_2896_;
goto v_resetjp_2869_;
}
else
{
lean_dec(v_l_2847_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2896_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2886_; 
v___x_2872_ = lean_nat_add(v___x_2842_, v_size_2843_);
v___x_2873_ = lean_nat_add(v___x_2872_, v_size_2844_);
lean_dec(v_size_2844_);
if (lean_obj_tag(v_l_2863_) == 0)
{
lean_object* v_size_2894_; 
v_size_2894_ = lean_ctor_get(v_l_2863_, 0);
lean_inc(v_size_2894_);
v___y_2886_ = v_size_2894_;
goto v___jp_2885_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_unsigned_to_nat(0u);
v___y_2886_ = v___x_2895_;
goto v___jp_2885_;
}
v___jp_2874_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = lean_nat_add(v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 4, v_r_2848_);
lean_ctor_set(v___x_2870_, 3, v_r_2864_);
lean_ctor_set(v___x_2870_, 2, v_v_2846_);
lean_ctor_set(v___x_2870_, 1, v_k_2845_);
lean_ctor_set(v___x_2870_, 0, v___x_2878_);
v___x_2880_ = v___x_2870_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_k_2845_);
lean_ctor_set(v_reuseFailAlloc_2884_, 2, v_v_2846_);
lean_ctor_set(v_reuseFailAlloc_2884_, 3, v_r_2864_);
lean_ctor_set(v_reuseFailAlloc_2884_, 4, v_r_2848_);
v___x_2880_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 4, v___x_2880_);
lean_ctor_set(v___x_2858_, 3, v___y_2875_);
lean_ctor_set(v___x_2858_, 2, v_v_2862_);
lean_ctor_set(v___x_2858_, 1, v_k_2861_);
lean_ctor_set(v___x_2858_, 0, v___x_2873_);
v___x_2882_ = v___x_2858_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_k_2861_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_v_2862_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v___y_2875_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
v___jp_2885_:
{
lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2887_ = lean_nat_add(v___x_2872_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec(v___x_2872_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_l_2863_);
lean_ctor_set(v___x_2838_, 3, v_impl_2841_);
lean_ctor_set(v___x_2838_, 0, v___x_2887_);
v___x_2889_ = v___x_2838_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2893_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2893_, 3, v_impl_2841_);
lean_ctor_set(v_reuseFailAlloc_2893_, 4, v_l_2863_);
v___x_2889_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_nat_add(v___x_2842_, v_size_2865_);
if (lean_obj_tag(v_r_2864_) == 0)
{
lean_object* v_size_2891_; 
v_size_2891_ = lean_ctor_get(v_r_2864_, 0);
lean_inc(v_size_2891_);
v___y_2875_ = v___x_2889_;
v___y_2876_ = v___x_2890_;
v___y_2877_ = v_size_2891_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_unsigned_to_nat(0u);
v___y_2875_ = v___x_2889_;
v___y_2876_ = v___x_2890_;
v___y_2877_ = v___x_2892_;
goto v___jp_2874_;
}
}
}
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
lean_del_object(v___x_2838_);
v___x_2902_ = lean_nat_add(v___x_2842_, v_size_2843_);
v___x_2903_ = lean_nat_add(v___x_2902_, v_size_2844_);
lean_dec(v_size_2844_);
v___x_2904_ = lean_nat_add(v___x_2902_, v_size_2860_);
lean_dec(v___x_2902_);
lean_inc_ref(v_impl_2841_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 4, v_l_2847_);
lean_ctor_set(v___x_2858_, 3, v_impl_2841_);
lean_ctor_set(v___x_2858_, 2, v_v_2834_);
lean_ctor_set(v___x_2858_, 1, v_k_2833_);
lean_ctor_set(v___x_2858_, 0, v___x_2904_);
v___x_2906_ = v___x_2858_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_impl_2841_);
lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_l_2847_);
v___x_2906_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_isSharedCheck_2913_ = !lean_is_exclusive(v_impl_2841_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2914_ = lean_ctor_get(v_impl_2841_, 4);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_impl_2841_, 3);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_impl_2841_, 2);
lean_dec(v_unused_2916_);
v_unused_2917_ = lean_ctor_get(v_impl_2841_, 1);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v_impl_2841_, 0);
lean_dec(v_unused_2918_);
v___x_2908_ = v_impl_2841_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v_impl_2841_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 4, v_r_2848_);
lean_ctor_set(v___x_2908_, 3, v___x_2906_);
lean_ctor_set(v___x_2908_, 2, v_v_2846_);
lean_ctor_set(v___x_2908_, 1, v_k_2845_);
lean_ctor_set(v___x_2908_, 0, v___x_2903_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2845_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2846_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2912_, 4, v_r_2848_);
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
}
else
{
lean_object* v_size_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v_size_2926_ = lean_ctor_get(v_impl_2841_, 0);
v___x_2927_ = lean_nat_add(v___x_2842_, v_size_2926_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 3, v_impl_2841_);
lean_ctor_set(v___x_2838_, 0, v___x_2927_);
v___x_2929_ = v___x_2838_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_impl_2841_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_r_2836_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
else
{
if (lean_obj_tag(v_r_2836_) == 0)
{
lean_object* v_l_2931_; 
v_l_2931_ = lean_ctor_get(v_r_2836_, 3);
lean_inc(v_l_2931_);
if (lean_obj_tag(v_l_2931_) == 0)
{
lean_object* v_r_2932_; 
v_r_2932_ = lean_ctor_get(v_r_2836_, 4);
lean_inc(v_r_2932_);
if (lean_obj_tag(v_r_2932_) == 0)
{
lean_object* v_size_2933_; lean_object* v_k_2934_; lean_object* v_v_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2948_; 
v_size_2933_ = lean_ctor_get(v_r_2836_, 0);
v_k_2934_ = lean_ctor_get(v_r_2836_, 1);
v_v_2935_ = lean_ctor_get(v_r_2836_, 2);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_2948_ == 0)
{
lean_object* v_unused_2949_; lean_object* v_unused_2950_; 
v_unused_2949_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_2950_);
v___x_2937_ = v_r_2836_;
v_isShared_2938_ = v_isSharedCheck_2948_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_v_2935_);
lean_inc(v_k_2934_);
lean_inc(v_size_2933_);
lean_dec(v_r_2836_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2948_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_size_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v_size_2939_ = lean_ctor_get(v_l_2931_, 0);
v___x_2940_ = lean_nat_add(v___x_2842_, v_size_2933_);
lean_dec(v_size_2933_);
v___x_2941_ = lean_nat_add(v___x_2842_, v_size_2939_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 4, v_l_2931_);
lean_ctor_set(v___x_2937_, 3, v_impl_2841_);
lean_ctor_set(v___x_2937_, 2, v_v_2834_);
lean_ctor_set(v___x_2937_, 1, v_k_2833_);
lean_ctor_set(v___x_2937_, 0, v___x_2941_);
v___x_2943_ = v___x_2937_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_impl_2841_);
lean_ctor_set(v_reuseFailAlloc_2947_, 4, v_l_2931_);
v___x_2943_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_r_2932_);
lean_ctor_set(v___x_2838_, 3, v___x_2943_);
lean_ctor_set(v___x_2838_, 2, v_v_2935_);
lean_ctor_set(v___x_2838_, 1, v_k_2934_);
lean_ctor_set(v___x_2838_, 0, v___x_2940_);
v___x_2945_ = v___x_2838_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_k_2934_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_v_2935_);
lean_ctor_set(v_reuseFailAlloc_2946_, 3, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2946_, 4, v_r_2932_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_k_2951_; lean_object* v_v_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2975_; 
v_k_2951_ = lean_ctor_get(v_r_2836_, 1);
v_v_2952_ = lean_ctor_get(v_r_2836_, 2);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; lean_object* v_unused_2977_; lean_object* v_unused_2978_; 
v_unused_2976_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_2976_);
v_unused_2977_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_2977_);
v_unused_2978_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_2978_);
v___x_2954_ = v_r_2836_;
v_isShared_2955_ = v_isSharedCheck_2975_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_v_2952_);
lean_inc(v_k_2951_);
lean_dec(v_r_2836_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2975_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_k_2956_; lean_object* v_v_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2971_; 
v_k_2956_ = lean_ctor_get(v_l_2931_, 1);
v_v_2957_ = lean_ctor_get(v_l_2931_, 2);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_l_2931_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; lean_object* v_unused_2973_; lean_object* v_unused_2974_; 
v_unused_2972_ = lean_ctor_get(v_l_2931_, 4);
lean_dec(v_unused_2972_);
v_unused_2973_ = lean_ctor_get(v_l_2931_, 3);
lean_dec(v_unused_2973_);
v_unused_2974_ = lean_ctor_get(v_l_2931_, 0);
lean_dec(v_unused_2974_);
v___x_2959_ = v_l_2931_;
v_isShared_2960_ = v_isSharedCheck_2971_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_v_2957_);
lean_inc(v_k_2956_);
lean_dec(v_l_2931_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2971_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(3u);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 4, v_r_2932_);
lean_ctor_set(v___x_2959_, 3, v_r_2932_);
lean_ctor_set(v___x_2959_, 2, v_v_2834_);
lean_ctor_set(v___x_2959_, 1, v_k_2833_);
lean_ctor_set(v___x_2959_, 0, v___x_2842_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2970_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2970_, 3, v_r_2932_);
lean_ctor_set(v_reuseFailAlloc_2970_, 4, v_r_2932_);
v___x_2963_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 3, v_r_2932_);
lean_ctor_set(v___x_2954_, 0, v___x_2842_);
v___x_2965_ = v___x_2954_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_k_2951_);
lean_ctor_set(v_reuseFailAlloc_2969_, 2, v_v_2952_);
lean_ctor_set(v_reuseFailAlloc_2969_, 3, v_r_2932_);
lean_ctor_set(v_reuseFailAlloc_2969_, 4, v_r_2932_);
v___x_2965_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2967_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_2965_);
lean_ctor_set(v___x_2838_, 3, v___x_2963_);
lean_ctor_set(v___x_2838_, 2, v_v_2957_);
lean_ctor_set(v___x_2838_, 1, v_k_2956_);
lean_ctor_set(v___x_2838_, 0, v___x_2961_);
v___x_2967_ = v___x_2838_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_k_2956_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_v_2957_);
lean_ctor_set(v_reuseFailAlloc_2968_, 3, v___x_2963_);
lean_ctor_set(v_reuseFailAlloc_2968_, 4, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2979_; 
v_r_2979_ = lean_ctor_get(v_r_2836_, 4);
lean_inc(v_r_2979_);
if (lean_obj_tag(v_r_2979_) == 0)
{
lean_object* v_k_2980_; lean_object* v_v_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2992_; 
v_k_2980_ = lean_ctor_get(v_r_2836_, 1);
v_v_2981_ = lean_ctor_get(v_r_2836_, 2);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; lean_object* v_unused_2994_; lean_object* v_unused_2995_; 
v_unused_2993_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_2993_);
v_unused_2994_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_2994_);
v_unused_2995_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_2995_);
v___x_2983_ = v_r_2836_;
v_isShared_2984_ = v_isSharedCheck_2992_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_v_2981_);
lean_inc(v_k_2980_);
lean_dec(v_r_2836_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2992_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2985_ = lean_unsigned_to_nat(3u);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 4, v_l_2931_);
lean_ctor_set(v___x_2983_, 2, v_v_2834_);
lean_ctor_set(v___x_2983_, 1, v_k_2833_);
lean_ctor_set(v___x_2983_, 0, v___x_2842_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_l_2931_);
lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_l_2931_);
v___x_2987_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2989_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_r_2979_);
lean_ctor_set(v___x_2838_, 3, v___x_2987_);
lean_ctor_set(v___x_2838_, 2, v_v_2981_);
lean_ctor_set(v___x_2838_, 1, v_k_2980_);
lean_ctor_set(v___x_2838_, 0, v___x_2985_);
v___x_2989_ = v___x_2838_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_k_2980_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_v_2981_);
lean_ctor_set(v_reuseFailAlloc_2990_, 3, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2990_, 4, v_r_2979_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
else
{
lean_object* v_size_2996_; lean_object* v_k_2997_; lean_object* v_v_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
v_size_2996_ = lean_ctor_get(v_r_2836_, 0);
v_k_2997_ = lean_ctor_get(v_r_2836_, 1);
v_v_2998_ = lean_ctor_get(v_r_2836_, 2);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; lean_object* v_unused_3011_; 
v_unused_3010_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_3010_);
v_unused_3011_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_3011_);
v___x_3000_ = v_r_2836_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_v_2998_);
lean_inc(v_k_2997_);
lean_inc(v_size_2996_);
lean_dec(v_r_2836_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 3, v_r_2979_);
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_size_2996_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_k_2997_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_v_2998_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_r_2979_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_r_2979_);
v___x_3003_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(2u);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_3003_);
lean_ctor_set(v___x_2838_, 3, v_r_2979_);
lean_ctor_set(v___x_2838_, 0, v___x_3004_);
v___x_3006_ = v___x_2838_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3007_, 3, v_r_2979_);
lean_ctor_set(v_reuseFailAlloc_3007_, 4, v___x_3003_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
}
else
{
lean_object* v___x_3013_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 3, v_r_2836_);
lean_ctor_set(v___x_2838_, 0, v___x_2842_);
v___x_3013_ = v___x_2838_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_2842_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_r_2836_);
lean_ctor_set(v_reuseFailAlloc_3014_, 4, v_r_2836_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2838_);
lean_dec(v_v_2834_);
lean_dec(v_k_2833_);
if (lean_obj_tag(v_l_2835_) == 0)
{
if (lean_obj_tag(v_r_2836_) == 0)
{
lean_object* v_size_3015_; lean_object* v_k_3016_; lean_object* v_v_3017_; lean_object* v_l_3018_; lean_object* v_r_3019_; lean_object* v_size_3020_; lean_object* v_k_3021_; lean_object* v_v_3022_; lean_object* v_l_3023_; lean_object* v_r_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_size_3015_ = lean_ctor_get(v_l_2835_, 0);
v_k_3016_ = lean_ctor_get(v_l_2835_, 1);
v_v_3017_ = lean_ctor_get(v_l_2835_, 2);
v_l_3018_ = lean_ctor_get(v_l_2835_, 3);
v_r_3019_ = lean_ctor_get(v_l_2835_, 4);
lean_inc(v_r_3019_);
v_size_3020_ = lean_ctor_get(v_r_2836_, 0);
v_k_3021_ = lean_ctor_get(v_r_2836_, 1);
v_v_3022_ = lean_ctor_get(v_r_2836_, 2);
v_l_3023_ = lean_ctor_get(v_r_2836_, 3);
lean_inc(v_l_3023_);
v_r_3024_ = lean_ctor_get(v_r_2836_, 4);
v___x_3025_ = lean_unsigned_to_nat(1u);
v___x_3026_ = lean_nat_dec_lt(v_size_3015_, v_size_3020_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3162_; 
lean_inc(v_l_3018_);
lean_inc(v_v_3017_);
lean_inc(v_k_3016_);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; lean_object* v_unused_3167_; 
v_unused_3163_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_l_2835_, 2);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_l_2835_, 1);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3167_);
v___x_3028_ = v_l_2835_;
v_isShared_3029_ = v_isSharedCheck_3162_;
goto v_resetjp_3027_;
}
else
{
lean_dec(v_l_2835_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3162_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v_tree_3031_; 
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3016_, v_v_3017_, v_l_3018_, v_r_3019_);
v_tree_3031_ = lean_ctor_get(v___x_3030_, 2);
if (lean_obj_tag(v_tree_3031_) == 0)
{
lean_object* v_k_3032_; lean_object* v_v_3033_; lean_object* v_size_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
lean_inc_ref(v_tree_3031_);
v_k_3032_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_k_3032_);
v_v_3033_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_v_3033_);
lean_dec_ref(v___x_3030_);
v_size_3034_ = lean_ctor_get(v_tree_3031_, 0);
v___x_3035_ = lean_unsigned_to_nat(3u);
v___x_3036_ = lean_nat_mul(v___x_3035_, v_size_3034_);
v___x_3037_ = lean_nat_dec_lt(v___x_3036_, v_size_3020_);
lean_dec(v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
lean_dec(v_l_3023_);
v___x_3038_ = lean_nat_add(v___x_3025_, v_size_3034_);
v___x_3039_ = lean_nat_add(v___x_3038_, v_size_3020_);
lean_dec(v___x_3038_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v_r_2836_);
lean_ctor_set(v___x_3028_, 3, v_tree_3031_);
lean_ctor_set(v___x_3028_, 2, v_v_3033_);
lean_ctor_set(v___x_3028_, 1, v_k_3032_);
lean_ctor_set(v___x_3028_, 0, v___x_3039_);
v___x_3041_ = v___x_3028_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_k_3032_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v_v_3033_);
lean_ctor_set(v_reuseFailAlloc_3042_, 3, v_tree_3031_);
lean_ctor_set(v_reuseFailAlloc_3042_, 4, v_r_2836_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
else
{
lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3097_; 
lean_inc(v_r_3024_);
lean_inc(v_v_3022_);
lean_inc(v_k_3021_);
lean_inc(v_size_3020_);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; lean_object* v_unused_3102_; 
v_unused_3098_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_r_2836_, 2);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_r_2836_, 1);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_3102_);
v___x_3044_ = v_r_2836_;
v_isShared_3045_ = v_isSharedCheck_3097_;
goto v_resetjp_3043_;
}
else
{
lean_dec(v_r_2836_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3097_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_size_3046_; lean_object* v_k_3047_; lean_object* v_v_3048_; lean_object* v_l_3049_; lean_object* v_r_3050_; lean_object* v_size_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v_size_3046_ = lean_ctor_get(v_l_3023_, 0);
v_k_3047_ = lean_ctor_get(v_l_3023_, 1);
v_v_3048_ = lean_ctor_get(v_l_3023_, 2);
v_l_3049_ = lean_ctor_get(v_l_3023_, 3);
v_r_3050_ = lean_ctor_get(v_l_3023_, 4);
v_size_3051_ = lean_ctor_get(v_r_3024_, 0);
v___x_3052_ = lean_unsigned_to_nat(2u);
v___x_3053_ = lean_nat_mul(v___x_3052_, v_size_3051_);
v___x_3054_ = lean_nat_dec_lt(v_size_3046_, v___x_3053_);
lean_dec(v___x_3053_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3082_; 
lean_inc(v_r_3050_);
lean_inc(v_l_3049_);
lean_inc(v_v_3048_);
lean_inc(v_k_3047_);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_l_3023_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; lean_object* v_unused_3084_; lean_object* v_unused_3085_; lean_object* v_unused_3086_; lean_object* v_unused_3087_; 
v_unused_3083_ = lean_ctor_get(v_l_3023_, 4);
lean_dec(v_unused_3083_);
v_unused_3084_ = lean_ctor_get(v_l_3023_, 3);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_l_3023_, 2);
lean_dec(v_unused_3085_);
v_unused_3086_ = lean_ctor_get(v_l_3023_, 1);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_l_3023_, 0);
lean_dec(v_unused_3087_);
v___x_3056_ = v_l_3023_;
v_isShared_3057_ = v_isSharedCheck_3082_;
goto v_resetjp_3055_;
}
else
{
lean_dec(v_l_3023_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3082_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3072_; 
v___x_3058_ = lean_nat_add(v___x_3025_, v_size_3034_);
v___x_3059_ = lean_nat_add(v___x_3058_, v_size_3020_);
lean_dec(v_size_3020_);
if (lean_obj_tag(v_l_3049_) == 0)
{
lean_object* v_size_3080_; 
v_size_3080_ = lean_ctor_get(v_l_3049_, 0);
lean_inc(v_size_3080_);
v___y_3072_ = v_size_3080_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___y_3072_ = v___x_3081_;
goto v___jp_3071_;
}
v___jp_3060_:
{
lean_object* v___x_3064_; lean_object* v___x_3066_; 
v___x_3064_ = lean_nat_add(v___y_3062_, v___y_3063_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 4, v_r_3024_);
lean_ctor_set(v___x_3056_, 3, v_r_3050_);
lean_ctor_set(v___x_3056_, 2, v_v_3022_);
lean_ctor_set(v___x_3056_, 1, v_k_3021_);
lean_ctor_set(v___x_3056_, 0, v___x_3064_);
v___x_3066_ = v___x_3056_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_r_3050_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_r_3024_);
v___x_3066_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 4, v___x_3066_);
lean_ctor_set(v___x_3044_, 3, v___y_3061_);
lean_ctor_set(v___x_3044_, 2, v_v_3048_);
lean_ctor_set(v___x_3044_, 1, v_k_3047_);
lean_ctor_set(v___x_3044_, 0, v___x_3059_);
v___x_3068_ = v___x_3044_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v_k_3047_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_v_3048_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v___y_3061_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
v___jp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_nat_add(v___x_3058_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec(v___x_3058_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v_l_3049_);
lean_ctor_set(v___x_3028_, 3, v_tree_3031_);
lean_ctor_set(v___x_3028_, 2, v_v_3033_);
lean_ctor_set(v___x_3028_, 1, v_k_3032_);
lean_ctor_set(v___x_3028_, 0, v___x_3073_);
v___x_3075_ = v___x_3028_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_k_3032_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_v_3033_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_tree_3031_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_l_3049_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_nat_add(v___x_3025_, v_size_3051_);
if (lean_obj_tag(v_r_3050_) == 0)
{
lean_object* v_size_3077_; 
v_size_3077_ = lean_ctor_get(v_r_3050_, 0);
lean_inc(v_size_3077_);
v___y_3061_ = v___x_3075_;
v___y_3062_ = v___x_3076_;
v___y_3063_ = v_size_3077_;
goto v___jp_3060_;
}
else
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_unsigned_to_nat(0u);
v___y_3061_ = v___x_3075_;
v___y_3062_ = v___x_3076_;
v___y_3063_ = v___x_3078_;
goto v___jp_3060_;
}
}
}
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3088_ = lean_nat_add(v___x_3025_, v_size_3034_);
v___x_3089_ = lean_nat_add(v___x_3088_, v_size_3020_);
lean_dec(v_size_3020_);
v___x_3090_ = lean_nat_add(v___x_3088_, v_size_3046_);
lean_dec(v___x_3088_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 4, v_l_3023_);
lean_ctor_set(v___x_3044_, 3, v_tree_3031_);
lean_ctor_set(v___x_3044_, 2, v_v_3033_);
lean_ctor_set(v___x_3044_, 1, v_k_3032_);
lean_ctor_set(v___x_3044_, 0, v___x_3090_);
v___x_3092_ = v___x_3044_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_k_3032_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_v_3033_);
lean_ctor_set(v_reuseFailAlloc_3096_, 3, v_tree_3031_);
lean_ctor_set(v_reuseFailAlloc_3096_, 4, v_l_3023_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v_r_3024_);
lean_ctor_set(v___x_3028_, 3, v___x_3092_);
lean_ctor_set(v___x_3028_, 2, v_v_3022_);
lean_ctor_set(v___x_3028_, 1, v_k_3021_);
lean_ctor_set(v___x_3028_, 0, v___x_3089_);
v___x_3094_ = v___x_3028_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_r_3024_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
}
else
{
lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3156_; 
lean_inc(v_r_3024_);
lean_inc(v_v_3022_);
lean_inc(v_k_3021_);
lean_inc(v_size_3020_);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; lean_object* v_unused_3161_; 
v_unused_3157_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_r_2836_, 2);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_r_2836_, 1);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_3161_);
v___x_3104_ = v_r_2836_;
v_isShared_3105_ = v_isSharedCheck_3156_;
goto v_resetjp_3103_;
}
else
{
lean_dec(v_r_2836_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3156_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
if (lean_obj_tag(v_l_3023_) == 0)
{
if (lean_obj_tag(v_r_3024_) == 0)
{
lean_object* v_k_3106_; lean_object* v_v_3107_; lean_object* v_size_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
lean_inc(v_tree_3031_);
v_k_3106_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_k_3106_);
v_v_3107_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_v_3107_);
lean_dec_ref(v___x_3030_);
v_size_3108_ = lean_ctor_get(v_l_3023_, 0);
v___x_3109_ = lean_nat_add(v___x_3025_, v_size_3020_);
lean_dec(v_size_3020_);
v___x_3110_ = lean_nat_add(v___x_3025_, v_size_3108_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 4, v_l_3023_);
lean_ctor_set(v___x_3104_, 3, v_tree_3031_);
lean_ctor_set(v___x_3104_, 2, v_v_3107_);
lean_ctor_set(v___x_3104_, 1, v_k_3106_);
lean_ctor_set(v___x_3104_, 0, v___x_3110_);
v___x_3112_ = v___x_3104_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_k_3106_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_v_3107_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_tree_3031_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_l_3023_);
v___x_3112_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3114_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v_r_3024_);
lean_ctor_set(v___x_3028_, 3, v___x_3112_);
lean_ctor_set(v___x_3028_, 2, v_v_3022_);
lean_ctor_set(v___x_3028_, 1, v_k_3021_);
lean_ctor_set(v___x_3028_, 0, v___x_3109_);
v___x_3114_ = v___x_3028_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_r_3024_);
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
lean_object* v_k_3117_; lean_object* v_v_3118_; lean_object* v_k_3119_; lean_object* v_v_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_size_3020_);
v_k_3117_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_k_3117_);
v_v_3118_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_v_3118_);
lean_dec_ref(v___x_3030_);
v_k_3119_ = lean_ctor_get(v_l_3023_, 1);
v_v_3120_ = lean_ctor_get(v_l_3023_, 2);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_l_3023_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3135_ = lean_ctor_get(v_l_3023_, 4);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_l_3023_, 3);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_l_3023_, 0);
lean_dec(v_unused_3137_);
v___x_3122_ = v_l_3023_;
v_isShared_3123_ = v_isSharedCheck_3134_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_v_3120_);
lean_inc(v_k_3119_);
lean_dec(v_l_3023_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3134_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_unsigned_to_nat(3u);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 4, v_r_3024_);
lean_ctor_set(v___x_3122_, 3, v_r_3024_);
lean_ctor_set(v___x_3122_, 2, v_v_3118_);
lean_ctor_set(v___x_3122_, 1, v_k_3117_);
lean_ctor_set(v___x_3122_, 0, v___x_3025_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_k_3117_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_v_3118_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_r_3024_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v_r_3024_);
v___x_3126_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 3, v_r_3024_);
lean_ctor_set(v___x_3104_, 0, v___x_3025_);
v___x_3128_ = v___x_3104_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_r_3024_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_r_3024_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___x_3128_);
lean_ctor_set(v___x_3028_, 3, v___x_3126_);
lean_ctor_set(v___x_3028_, 2, v_v_3120_);
lean_ctor_set(v___x_3028_, 1, v_k_3119_);
lean_ctor_set(v___x_3028_, 0, v___x_3124_);
v___x_3130_ = v___x_3028_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3119_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3120_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v___x_3128_);
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
else
{
if (lean_obj_tag(v_r_3024_) == 0)
{
lean_object* v_k_3138_; lean_object* v_v_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
lean_dec(v_size_3020_);
v_k_3138_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_k_3138_);
v_v_3139_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_v_3139_);
lean_dec_ref(v___x_3030_);
v___x_3140_ = lean_unsigned_to_nat(3u);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 4, v_l_3023_);
lean_ctor_set(v___x_3104_, 2, v_v_3139_);
lean_ctor_set(v___x_3104_, 1, v_k_3138_);
lean_ctor_set(v___x_3104_, 0, v___x_3025_);
v___x_3142_ = v___x_3104_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_k_3138_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_v_3139_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_l_3023_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_l_3023_);
v___x_3142_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v_r_3024_);
lean_ctor_set(v___x_3028_, 3, v___x_3142_);
lean_ctor_set(v___x_3028_, 2, v_v_3022_);
lean_ctor_set(v___x_3028_, 1, v_k_3021_);
lean_ctor_set(v___x_3028_, 0, v___x_3140_);
v___x_3144_ = v___x_3028_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_r_3024_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v_k_3147_; lean_object* v_v_3148_; lean_object* v___x_3150_; 
v_k_3147_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_k_3147_);
v_v_3148_ = lean_ctor_get(v___x_3030_, 1);
lean_inc(v_v_3148_);
lean_dec_ref(v___x_3030_);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 3, v_r_3024_);
v___x_3150_ = v___x_3104_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_size_3020_);
lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_k_3021_);
lean_ctor_set(v_reuseFailAlloc_3155_, 2, v_v_3022_);
lean_ctor_set(v_reuseFailAlloc_3155_, 3, v_r_3024_);
lean_ctor_set(v_reuseFailAlloc_3155_, 4, v_r_3024_);
v___x_3150_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___x_3151_ = lean_unsigned_to_nat(2u);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 4, v___x_3150_);
lean_ctor_set(v___x_3028_, 3, v_r_3024_);
lean_ctor_set(v___x_3028_, 2, v_v_3148_);
lean_ctor_set(v___x_3028_, 1, v_k_3147_);
lean_ctor_set(v___x_3028_, 0, v___x_3151_);
v___x_3153_ = v___x_3028_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_k_3147_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_v_3148_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_r_3024_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v___x_3150_);
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
}
}
else
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3320_; 
lean_inc(v_r_3024_);
lean_inc(v_v_3022_);
lean_inc(v_k_3021_);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_r_2836_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; 
v_unused_3321_ = lean_ctor_get(v_r_2836_, 4);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_r_2836_, 3);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_r_2836_, 2);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_r_2836_, 1);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_r_2836_, 0);
lean_dec(v_unused_3325_);
v___x_3169_ = v_r_2836_;
v_isShared_3170_ = v_isSharedCheck_3320_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v_r_2836_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3320_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v_tree_3172_; 
v___x_3171_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3021_, v_v_3022_, v_l_3023_, v_r_3024_);
v_tree_3172_ = lean_ctor_get(v___x_3171_, 2);
lean_inc(v_tree_3172_);
if (lean_obj_tag(v_tree_3172_) == 0)
{
lean_object* v_k_3173_; lean_object* v_v_3174_; lean_object* v_size_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_k_3173_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_k_3173_);
v_v_3174_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_v_3174_);
lean_dec_ref(v___x_3171_);
v_size_3175_ = lean_ctor_get(v_tree_3172_, 0);
v___x_3176_ = lean_unsigned_to_nat(3u);
v___x_3177_ = lean_nat_mul(v___x_3176_, v_size_3175_);
v___x_3178_ = lean_nat_dec_lt(v___x_3177_, v_size_3015_);
lean_dec(v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
lean_dec(v_r_3019_);
v___x_3179_ = lean_nat_add(v___x_3025_, v_size_3015_);
v___x_3180_ = lean_nat_add(v___x_3179_, v_size_3175_);
lean_dec(v___x_3179_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_tree_3172_);
lean_ctor_set(v___x_3169_, 3, v_l_2835_);
lean_ctor_set(v___x_3169_, 2, v_v_3174_);
lean_ctor_set(v___x_3169_, 1, v_k_3173_);
lean_ctor_set(v___x_3169_, 0, v___x_3180_);
v___x_3182_ = v___x_3169_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_tree_3172_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
else
{
lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3249_; 
lean_inc(v_l_3018_);
lean_inc(v_v_3017_);
lean_inc(v_k_3016_);
lean_inc(v_size_3015_);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; lean_object* v_unused_3253_; lean_object* v_unused_3254_; 
v_unused_3250_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_l_2835_, 2);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_l_2835_, 1);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3254_);
v___x_3185_ = v_l_2835_;
v_isShared_3186_ = v_isSharedCheck_3249_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v_l_2835_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3249_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_size_3187_; lean_object* v_size_3188_; lean_object* v_k_3189_; lean_object* v_v_3190_; lean_object* v_l_3191_; lean_object* v_r_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_size_3187_ = lean_ctor_get(v_l_3018_, 0);
v_size_3188_ = lean_ctor_get(v_r_3019_, 0);
v_k_3189_ = lean_ctor_get(v_r_3019_, 1);
v_v_3190_ = lean_ctor_get(v_r_3019_, 2);
v_l_3191_ = lean_ctor_get(v_r_3019_, 3);
v_r_3192_ = lean_ctor_get(v_r_3019_, 4);
v___x_3193_ = lean_unsigned_to_nat(2u);
v___x_3194_ = lean_nat_mul(v___x_3193_, v_size_3187_);
v___x_3195_ = lean_nat_dec_lt(v_size_3188_, v___x_3194_);
lean_dec(v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3233_; 
lean_inc(v_r_3192_);
lean_inc(v_l_3191_);
lean_inc(v_v_3190_);
lean_inc(v_k_3189_);
lean_del_object(v___x_3185_);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_r_3019_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; lean_object* v_unused_3237_; lean_object* v_unused_3238_; 
v_unused_3234_ = lean_ctor_get(v_r_3019_, 4);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_r_3019_, 3);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_r_3019_, 2);
lean_dec(v_unused_3236_);
v_unused_3237_ = lean_ctor_get(v_r_3019_, 1);
lean_dec(v_unused_3237_);
v_unused_3238_ = lean_ctor_get(v_r_3019_, 0);
lean_dec(v_unused_3238_);
v___x_3197_ = v_r_3019_;
v_isShared_3198_ = v_isSharedCheck_3233_;
goto v_resetjp_3196_;
}
else
{
lean_dec(v_r_3019_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3233_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___x_3221_; lean_object* v___y_3223_; 
v___x_3199_ = lean_nat_add(v___x_3025_, v_size_3015_);
lean_dec(v_size_3015_);
v___x_3200_ = lean_nat_add(v___x_3199_, v_size_3175_);
lean_dec(v___x_3199_);
v___x_3221_ = lean_nat_add(v___x_3025_, v_size_3187_);
if (lean_obj_tag(v_l_3191_) == 0)
{
lean_object* v_size_3231_; 
v_size_3231_ = lean_ctor_get(v_l_3191_, 0);
lean_inc(v_size_3231_);
v___y_3223_ = v_size_3231_;
goto v___jp_3222_;
}
else
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_unsigned_to_nat(0u);
v___y_3223_ = v___x_3232_;
goto v___jp_3222_;
}
v___jp_3201_:
{
lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3205_ = lean_nat_add(v___y_3202_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec(v___y_3202_);
lean_inc_ref(v_tree_3172_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 4, v_tree_3172_);
lean_ctor_set(v___x_3197_, 3, v_r_3192_);
lean_ctor_set(v___x_3197_, 2, v_v_3174_);
lean_ctor_set(v___x_3197_, 1, v_k_3173_);
lean_ctor_set(v___x_3197_, 0, v___x_3205_);
v___x_3207_ = v___x_3197_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_r_3192_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_tree_3172_);
v___x_3207_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_isSharedCheck_3214_ = !lean_is_exclusive(v_tree_3172_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; lean_object* v_unused_3218_; lean_object* v_unused_3219_; 
v_unused_3215_ = lean_ctor_get(v_tree_3172_, 4);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_tree_3172_, 3);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_tree_3172_, 2);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_tree_3172_, 1);
lean_dec(v_unused_3218_);
v_unused_3219_ = lean_ctor_get(v_tree_3172_, 0);
lean_dec(v_unused_3219_);
v___x_3209_ = v_tree_3172_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v_tree_3172_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 4, v___x_3207_);
lean_ctor_set(v___x_3209_, 3, v___y_3203_);
lean_ctor_set(v___x_3209_, 2, v_v_3190_);
lean_ctor_set(v___x_3209_, 1, v_k_3189_);
lean_ctor_set(v___x_3209_, 0, v___x_3200_);
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_k_3189_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_v_3190_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v___y_3203_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v___x_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
v___jp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3224_ = lean_nat_add(v___x_3221_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec(v___x_3221_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_l_3191_);
lean_ctor_set(v___x_3169_, 3, v_l_3018_);
lean_ctor_set(v___x_3169_, 2, v_v_3017_);
lean_ctor_set(v___x_3169_, 1, v_k_3016_);
lean_ctor_set(v___x_3169_, 0, v___x_3224_);
v___x_3226_ = v___x_3169_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_k_3016_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_v_3017_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v_l_3191_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_nat_add(v___x_3025_, v_size_3175_);
if (lean_obj_tag(v_r_3192_) == 0)
{
lean_object* v_size_3228_; 
v_size_3228_ = lean_ctor_get(v_r_3192_, 0);
lean_inc(v_size_3228_);
v___y_3202_ = v___x_3227_;
v___y_3203_ = v___x_3226_;
v___y_3204_ = v_size_3228_;
goto v___jp_3201_;
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_unsigned_to_nat(0u);
v___y_3202_ = v___x_3227_;
v___y_3203_ = v___x_3226_;
v___y_3204_ = v___x_3229_;
goto v___jp_3201_;
}
}
}
}
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3239_ = lean_nat_add(v___x_3025_, v_size_3015_);
lean_dec(v_size_3015_);
v___x_3240_ = lean_nat_add(v___x_3239_, v_size_3175_);
lean_dec(v___x_3239_);
v___x_3241_ = lean_nat_add(v___x_3025_, v_size_3175_);
v___x_3242_ = lean_nat_add(v___x_3241_, v_size_3188_);
lean_dec(v___x_3241_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_tree_3172_);
lean_ctor_set(v___x_3169_, 3, v_r_3019_);
lean_ctor_set(v___x_3169_, 2, v_v_3174_);
lean_ctor_set(v___x_3169_, 1, v_k_3173_);
lean_ctor_set(v___x_3169_, 0, v___x_3242_);
v___x_3244_ = v___x_3169_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_k_3173_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_v_3174_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_r_3019_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v_tree_3172_);
v___x_3244_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3246_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 4, v___x_3244_);
lean_ctor_set(v___x_3185_, 0, v___x_3240_);
v___x_3246_ = v___x_3185_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_k_3016_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_v_3017_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3018_) == 0)
{
lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3278_; 
lean_inc_ref(v_l_3018_);
lean_inc(v_v_3017_);
lean_inc(v_k_3016_);
lean_inc(v_size_3015_);
v_isSharedCheck_3278_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; lean_object* v_unused_3280_; lean_object* v_unused_3281_; lean_object* v_unused_3282_; lean_object* v_unused_3283_; 
v_unused_3279_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_l_2835_, 2);
lean_dec(v_unused_3281_);
v_unused_3282_ = lean_ctor_get(v_l_2835_, 1);
lean_dec(v_unused_3282_);
v_unused_3283_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3283_);
v___x_3256_ = v_l_2835_;
v_isShared_3257_ = v_isSharedCheck_3278_;
goto v_resetjp_3255_;
}
else
{
lean_dec(v_l_2835_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3278_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
if (lean_obj_tag(v_r_3019_) == 0)
{
lean_object* v_k_3258_; lean_object* v_v_3259_; lean_object* v_size_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
v_k_3258_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_k_3258_);
v_v_3259_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_v_3259_);
lean_dec_ref(v___x_3171_);
v_size_3260_ = lean_ctor_get(v_r_3019_, 0);
v___x_3261_ = lean_nat_add(v___x_3025_, v_size_3015_);
lean_dec(v_size_3015_);
v___x_3262_ = lean_nat_add(v___x_3025_, v_size_3260_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_tree_3172_);
lean_ctor_set(v___x_3169_, 3, v_r_3019_);
lean_ctor_set(v___x_3169_, 2, v_v_3259_);
lean_ctor_set(v___x_3169_, 1, v_k_3258_);
lean_ctor_set(v___x_3169_, 0, v___x_3262_);
v___x_3264_ = v___x_3169_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_k_3258_);
lean_ctor_set(v_reuseFailAlloc_3268_, 2, v_v_3259_);
lean_ctor_set(v_reuseFailAlloc_3268_, 3, v_r_3019_);
lean_ctor_set(v_reuseFailAlloc_3268_, 4, v_tree_3172_);
v___x_3264_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3266_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 4, v___x_3264_);
lean_ctor_set(v___x_3256_, 0, v___x_3261_);
v___x_3266_ = v___x_3256_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_k_3016_);
lean_ctor_set(v_reuseFailAlloc_3267_, 2, v_v_3017_);
lean_ctor_set(v_reuseFailAlloc_3267_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3267_, 4, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_object* v_k_3269_; lean_object* v_v_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
lean_dec(v_size_3015_);
v_k_3269_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_k_3269_);
v_v_3270_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_v_3270_);
lean_dec_ref(v___x_3171_);
v___x_3271_ = lean_unsigned_to_nat(3u);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_r_3019_);
lean_ctor_set(v___x_3169_, 3, v_r_3019_);
lean_ctor_set(v___x_3169_, 2, v_v_3270_);
lean_ctor_set(v___x_3169_, 1, v_k_3269_);
lean_ctor_set(v___x_3169_, 0, v___x_3025_);
v___x_3273_ = v___x_3169_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_k_3269_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_v_3270_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v_r_3019_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v_r_3019_);
v___x_3273_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3275_; 
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 4, v___x_3273_);
lean_ctor_set(v___x_3256_, 0, v___x_3271_);
v___x_3275_ = v___x_3256_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_k_3016_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_v_3017_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3019_) == 0)
{
lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3308_; 
lean_inc(v_l_3018_);
lean_inc(v_v_3017_);
lean_inc(v_k_3016_);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; 
v_unused_3309_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_2835_, 2);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_l_2835_, 1);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3313_);
v___x_3285_ = v_l_2835_;
v_isShared_3286_ = v_isSharedCheck_3308_;
goto v_resetjp_3284_;
}
else
{
lean_dec(v_l_2835_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3308_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_k_3287_; lean_object* v_v_3288_; lean_object* v_k_3289_; lean_object* v_v_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3304_; 
v_k_3287_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_k_3287_);
v_v_3288_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_v_3288_);
lean_dec_ref(v___x_3171_);
v_k_3289_ = lean_ctor_get(v_r_3019_, 1);
v_v_3290_ = lean_ctor_get(v_r_3019_, 2);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_r_3019_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; lean_object* v_unused_3306_; lean_object* v_unused_3307_; 
v_unused_3305_ = lean_ctor_get(v_r_3019_, 4);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_r_3019_, 3);
lean_dec(v_unused_3306_);
v_unused_3307_ = lean_ctor_get(v_r_3019_, 0);
lean_dec(v_unused_3307_);
v___x_3292_ = v_r_3019_;
v_isShared_3293_ = v_isSharedCheck_3304_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_v_3290_);
lean_inc(v_k_3289_);
lean_dec(v_r_3019_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3304_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3294_ = lean_unsigned_to_nat(3u);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 4, v_l_3018_);
lean_ctor_set(v___x_3292_, 3, v_l_3018_);
lean_ctor_set(v___x_3292_, 2, v_v_3017_);
lean_ctor_set(v___x_3292_, 1, v_k_3016_);
lean_ctor_set(v___x_3292_, 0, v___x_3025_);
v___x_3296_ = v___x_3292_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_k_3016_);
lean_ctor_set(v_reuseFailAlloc_3303_, 2, v_v_3017_);
lean_ctor_set(v_reuseFailAlloc_3303_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3303_, 4, v_l_3018_);
v___x_3296_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_l_3018_);
lean_ctor_set(v___x_3169_, 3, v_l_3018_);
lean_ctor_set(v___x_3169_, 2, v_v_3288_);
lean_ctor_set(v___x_3169_, 1, v_k_3287_);
lean_ctor_set(v___x_3169_, 0, v___x_3025_);
v___x_3298_ = v___x_3169_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_k_3287_);
lean_ctor_set(v_reuseFailAlloc_3302_, 2, v_v_3288_);
lean_ctor_set(v_reuseFailAlloc_3302_, 3, v_l_3018_);
lean_ctor_set(v_reuseFailAlloc_3302_, 4, v_l_3018_);
v___x_3298_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3300_; 
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 4, v___x_3298_);
lean_ctor_set(v___x_3285_, 3, v___x_3296_);
lean_ctor_set(v___x_3285_, 2, v_v_3290_);
lean_ctor_set(v___x_3285_, 1, v_k_3289_);
lean_ctor_set(v___x_3285_, 0, v___x_3294_);
v___x_3300_ = v___x_3285_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3289_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3290_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
}
}
else
{
lean_object* v_k_3314_; lean_object* v_v_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v_k_3314_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_k_3314_);
v_v_3315_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_v_3315_);
lean_dec_ref(v___x_3171_);
v___x_3316_ = lean_unsigned_to_nat(2u);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 4, v_r_3019_);
lean_ctor_set(v___x_3169_, 3, v_l_2835_);
lean_ctor_set(v___x_3169_, 2, v_v_3315_);
lean_ctor_set(v___x_3169_, 1, v_k_3314_);
lean_ctor_set(v___x_3169_, 0, v___x_3316_);
v___x_3318_ = v___x_3169_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_k_3314_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_v_3315_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v_r_3019_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
}
}
else
{
return v_l_2835_;
}
}
else
{
return v_r_2836_;
}
}
default: 
{
lean_object* v_impl_3326_; lean_object* v___x_3327_; 
v_impl_3326_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2831_, v_r_2836_);
v___x_3327_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3326_) == 0)
{
if (lean_obj_tag(v_l_2835_) == 0)
{
lean_object* v_size_3328_; lean_object* v_size_3329_; lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v_l_3332_; lean_object* v_r_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; 
v_size_3328_ = lean_ctor_get(v_impl_3326_, 0);
v_size_3329_ = lean_ctor_get(v_l_2835_, 0);
v_k_3330_ = lean_ctor_get(v_l_2835_, 1);
v_v_3331_ = lean_ctor_get(v_l_2835_, 2);
v_l_3332_ = lean_ctor_get(v_l_2835_, 3);
v_r_3333_ = lean_ctor_get(v_l_2835_, 4);
lean_inc(v_r_3333_);
v___x_3334_ = lean_unsigned_to_nat(3u);
v___x_3335_ = lean_nat_mul(v___x_3334_, v_size_3328_);
v___x_3336_ = lean_nat_dec_lt(v___x_3335_, v_size_3329_);
lean_dec(v___x_3335_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
lean_dec(v_r_3333_);
v___x_3337_ = lean_nat_add(v___x_3327_, v_size_3329_);
v___x_3338_ = lean_nat_add(v___x_3337_, v_size_3328_);
lean_dec(v___x_3337_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_impl_3326_);
lean_ctor_set(v___x_2838_, 0, v___x_3338_);
v___x_3340_ = v___x_2838_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_impl_3326_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
else
{
lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3407_; 
lean_inc(v_l_3332_);
lean_inc(v_v_3331_);
lean_inc(v_k_3330_);
lean_inc(v_size_3329_);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; 
v_unused_3408_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_l_2835_, 2);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_l_2835_, 1);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3412_);
v___x_3343_ = v_l_2835_;
v_isShared_3344_ = v_isSharedCheck_3407_;
goto v_resetjp_3342_;
}
else
{
lean_dec(v_l_2835_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3407_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_size_3345_; lean_object* v_size_3346_; lean_object* v_k_3347_; lean_object* v_v_3348_; lean_object* v_l_3349_; lean_object* v_r_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; uint8_t v___x_3353_; 
v_size_3345_ = lean_ctor_get(v_l_3332_, 0);
v_size_3346_ = lean_ctor_get(v_r_3333_, 0);
v_k_3347_ = lean_ctor_get(v_r_3333_, 1);
v_v_3348_ = lean_ctor_get(v_r_3333_, 2);
v_l_3349_ = lean_ctor_get(v_r_3333_, 3);
v_r_3350_ = lean_ctor_get(v_r_3333_, 4);
v___x_3351_ = lean_unsigned_to_nat(2u);
v___x_3352_ = lean_nat_mul(v___x_3351_, v_size_3345_);
v___x_3353_ = lean_nat_dec_lt(v_size_3346_, v___x_3352_);
lean_dec(v___x_3352_);
if (v___x_3353_ == 0)
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3382_; 
lean_inc(v_r_3350_);
lean_inc(v_l_3349_);
lean_inc(v_v_3348_);
lean_inc(v_k_3347_);
v_isSharedCheck_3382_ = !lean_is_exclusive(v_r_3333_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; lean_object* v_unused_3386_; lean_object* v_unused_3387_; 
v_unused_3383_ = lean_ctor_get(v_r_3333_, 4);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3333_, 3);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3333_, 2);
lean_dec(v_unused_3385_);
v_unused_3386_ = lean_ctor_get(v_r_3333_, 1);
lean_dec(v_unused_3386_);
v_unused_3387_ = lean_ctor_get(v_r_3333_, 0);
lean_dec(v_unused_3387_);
v___x_3355_ = v_r_3333_;
v_isShared_3356_ = v_isSharedCheck_3382_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v_r_3333_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3382_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___x_3370_; lean_object* v___y_3372_; 
v___x_3357_ = lean_nat_add(v___x_3327_, v_size_3329_);
lean_dec(v_size_3329_);
v___x_3358_ = lean_nat_add(v___x_3357_, v_size_3328_);
lean_dec(v___x_3357_);
v___x_3370_ = lean_nat_add(v___x_3327_, v_size_3345_);
if (lean_obj_tag(v_l_3349_) == 0)
{
lean_object* v_size_3380_; 
v_size_3380_ = lean_ctor_get(v_l_3349_, 0);
lean_inc(v_size_3380_);
v___y_3372_ = v_size_3380_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___y_3372_ = v___x_3381_;
goto v___jp_3371_;
}
v___jp_3359_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_nat_add(v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec(v___y_3361_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 4, v_impl_3326_);
lean_ctor_set(v___x_3355_, 3, v_r_3350_);
lean_ctor_set(v___x_3355_, 2, v_v_2834_);
lean_ctor_set(v___x_3355_, 1, v_k_2833_);
lean_ctor_set(v___x_3355_, 0, v___x_3363_);
v___x_3365_ = v___x_3355_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_r_3350_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_impl_3326_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v___x_3365_);
lean_ctor_set(v___x_3343_, 3, v___y_3360_);
lean_ctor_set(v___x_3343_, 2, v_v_3348_);
lean_ctor_set(v___x_3343_, 1, v_k_3347_);
lean_ctor_set(v___x_3343_, 0, v___x_3358_);
v___x_3367_ = v___x_3343_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3347_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3348_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v___y_3360_);
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
v___jp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_nat_add(v___x_3370_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec(v___x_3370_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_l_3349_);
lean_ctor_set(v___x_2838_, 3, v_l_3332_);
lean_ctor_set(v___x_2838_, 2, v_v_3331_);
lean_ctor_set(v___x_2838_, 1, v_k_3330_);
lean_ctor_set(v___x_2838_, 0, v___x_3373_);
v___x_3375_ = v___x_2838_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_l_3349_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_nat_add(v___x_3327_, v_size_3328_);
if (lean_obj_tag(v_r_3350_) == 0)
{
lean_object* v_size_3377_; 
v_size_3377_ = lean_ctor_get(v_r_3350_, 0);
lean_inc(v_size_3377_);
v___y_3360_ = v___x_3375_;
v___y_3361_ = v___x_3376_;
v___y_3362_ = v_size_3377_;
goto v___jp_3359_;
}
else
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_unsigned_to_nat(0u);
v___y_3360_ = v___x_3375_;
v___y_3361_ = v___x_3376_;
v___y_3362_ = v___x_3378_;
goto v___jp_3359_;
}
}
}
}
}
else
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
lean_del_object(v___x_2838_);
v___x_3388_ = lean_nat_add(v___x_3327_, v_size_3329_);
lean_dec(v_size_3329_);
v___x_3389_ = lean_nat_add(v___x_3388_, v_size_3328_);
lean_dec(v___x_3388_);
v___x_3390_ = lean_nat_add(v___x_3327_, v_size_3328_);
v___x_3391_ = lean_nat_add(v___x_3390_, v_size_3346_);
lean_dec(v___x_3390_);
lean_inc_ref(v_impl_3326_);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 4, v_impl_3326_);
lean_ctor_set(v___x_3343_, 3, v_r_3333_);
lean_ctor_set(v___x_3343_, 2, v_v_2834_);
lean_ctor_set(v___x_3343_, 1, v_k_2833_);
lean_ctor_set(v___x_3343_, 0, v___x_3391_);
v___x_3393_ = v___x_3343_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3391_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_r_3333_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v_impl_3326_);
v___x_3393_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
v_isSharedCheck_3400_ = !lean_is_exclusive(v_impl_3326_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; lean_object* v_unused_3405_; 
v_unused_3401_ = lean_ctor_get(v_impl_3326_, 4);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_impl_3326_, 3);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_impl_3326_, 2);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_impl_3326_, 1);
lean_dec(v_unused_3404_);
v_unused_3405_ = lean_ctor_get(v_impl_3326_, 0);
lean_dec(v_unused_3405_);
v___x_3395_ = v_impl_3326_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v_impl_3326_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 4, v___x_3393_);
lean_ctor_set(v___x_3395_, 3, v_l_3332_);
lean_ctor_set(v___x_3395_, 2, v_v_3331_);
lean_ctor_set(v___x_3395_, 1, v_k_3330_);
lean_ctor_set(v___x_3395_, 0, v___x_3389_);
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3399_, 3, v_l_3332_);
lean_ctor_set(v_reuseFailAlloc_3399_, 4, v___x_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3413_; lean_object* v___x_3414_; lean_object* v___x_3416_; 
v_size_3413_ = lean_ctor_get(v_impl_3326_, 0);
v___x_3414_ = lean_nat_add(v___x_3327_, v_size_3413_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_impl_3326_);
lean_ctor_set(v___x_2838_, 0, v___x_3414_);
v___x_3416_ = v___x_2838_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_impl_3326_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
else
{
if (lean_obj_tag(v_l_2835_) == 0)
{
lean_object* v_l_3418_; 
v_l_3418_ = lean_ctor_get(v_l_2835_, 3);
if (lean_obj_tag(v_l_3418_) == 0)
{
lean_object* v_r_3419_; 
lean_inc_ref(v_l_3418_);
v_r_3419_ = lean_ctor_get(v_l_2835_, 4);
lean_inc(v_r_3419_);
if (lean_obj_tag(v_r_3419_) == 0)
{
lean_object* v_size_3420_; lean_object* v_k_3421_; lean_object* v_v_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3435_; 
v_size_3420_ = lean_ctor_get(v_l_2835_, 0);
v_k_3421_ = lean_ctor_get(v_l_2835_, 1);
v_v_3422_ = lean_ctor_get(v_l_2835_, 2);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3436_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3437_);
v___x_3424_ = v_l_2835_;
v_isShared_3425_ = v_isSharedCheck_3435_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_v_3422_);
lean_inc(v_k_3421_);
lean_inc(v_size_3420_);
lean_dec(v_l_2835_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3435_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_size_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3430_; 
v_size_3426_ = lean_ctor_get(v_r_3419_, 0);
v___x_3427_ = lean_nat_add(v___x_3327_, v_size_3420_);
lean_dec(v_size_3420_);
v___x_3428_ = lean_nat_add(v___x_3327_, v_size_3426_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 4, v_impl_3326_);
lean_ctor_set(v___x_3424_, 3, v_r_3419_);
lean_ctor_set(v___x_3424_, 2, v_v_2834_);
lean_ctor_set(v___x_3424_, 1, v_k_2833_);
lean_ctor_set(v___x_3424_, 0, v___x_3428_);
v___x_3430_ = v___x_3424_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_r_3419_);
lean_ctor_set(v_reuseFailAlloc_3434_, 4, v_impl_3326_);
v___x_3430_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3432_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_3430_);
lean_ctor_set(v___x_2838_, 3, v_l_3418_);
lean_ctor_set(v___x_2838_, 2, v_v_3422_);
lean_ctor_set(v___x_2838_, 1, v_k_3421_);
lean_ctor_set(v___x_2838_, 0, v___x_3427_);
v___x_3432_ = v___x_2838_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3427_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_k_3421_);
lean_ctor_set(v_reuseFailAlloc_3433_, 2, v_v_3422_);
lean_ctor_set(v_reuseFailAlloc_3433_, 3, v_l_3418_);
lean_ctor_set(v_reuseFailAlloc_3433_, 4, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_k_3438_; lean_object* v_v_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3450_; 
v_k_3438_ = lean_ctor_get(v_l_2835_, 1);
v_v_3439_ = lean_ctor_get(v_l_2835_, 2);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3451_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3453_);
v___x_3441_ = v_l_2835_;
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_v_3439_);
lean_inc(v_k_3438_);
lean_dec(v_l_2835_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_unsigned_to_nat(3u);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 3, v_r_3419_);
lean_ctor_set(v___x_3441_, 2, v_v_2834_);
lean_ctor_set(v___x_3441_, 1, v_k_2833_);
lean_ctor_set(v___x_3441_, 0, v___x_3327_);
v___x_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3449_, 3, v_r_3419_);
lean_ctor_set(v_reuseFailAlloc_3449_, 4, v_r_3419_);
v___x_3445_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3447_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_3445_);
lean_ctor_set(v___x_2838_, 3, v_l_3418_);
lean_ctor_set(v___x_2838_, 2, v_v_3439_);
lean_ctor_set(v___x_2838_, 1, v_k_3438_);
lean_ctor_set(v___x_2838_, 0, v___x_3443_);
v___x_3447_ = v___x_2838_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_k_3438_);
lean_ctor_set(v_reuseFailAlloc_3448_, 2, v_v_3439_);
lean_ctor_set(v_reuseFailAlloc_3448_, 3, v_l_3418_);
lean_ctor_set(v_reuseFailAlloc_3448_, 4, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
else
{
lean_object* v_r_3454_; 
v_r_3454_ = lean_ctor_get(v_l_2835_, 4);
lean_inc(v_r_3454_);
if (lean_obj_tag(v_r_3454_) == 0)
{
lean_object* v_k_3455_; lean_object* v_v_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3479_; 
lean_inc(v_l_3418_);
v_k_3455_ = lean_ctor_get(v_l_2835_, 1);
v_v_3456_ = lean_ctor_get(v_l_2835_, 2);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_l_2835_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; lean_object* v_unused_3481_; lean_object* v_unused_3482_; 
v_unused_3480_ = lean_ctor_get(v_l_2835_, 4);
lean_dec(v_unused_3480_);
v_unused_3481_ = lean_ctor_get(v_l_2835_, 3);
lean_dec(v_unused_3481_);
v_unused_3482_ = lean_ctor_get(v_l_2835_, 0);
lean_dec(v_unused_3482_);
v___x_3458_ = v_l_2835_;
v_isShared_3459_ = v_isSharedCheck_3479_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_v_3456_);
lean_inc(v_k_3455_);
lean_dec(v_l_2835_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3479_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_k_3460_; lean_object* v_v_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3475_; 
v_k_3460_ = lean_ctor_get(v_r_3454_, 1);
v_v_3461_ = lean_ctor_get(v_r_3454_, 2);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_r_3454_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3476_ = lean_ctor_get(v_r_3454_, 4);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_r_3454_, 3);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_r_3454_, 0);
lean_dec(v_unused_3478_);
v___x_3463_ = v_r_3454_;
v_isShared_3464_ = v_isSharedCheck_3475_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_v_3461_);
lean_inc(v_k_3460_);
lean_dec(v_r_3454_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3475_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3465_ = lean_unsigned_to_nat(3u);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 4, v_l_3418_);
lean_ctor_set(v___x_3463_, 3, v_l_3418_);
lean_ctor_set(v___x_3463_, 2, v_v_3456_);
lean_ctor_set(v___x_3463_, 1, v_k_3455_);
lean_ctor_set(v___x_3463_, 0, v___x_3327_);
v___x_3467_ = v___x_3463_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_k_3455_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_v_3456_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_l_3418_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_l_3418_);
v___x_3467_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 4, v_l_3418_);
lean_ctor_set(v___x_3458_, 2, v_v_2834_);
lean_ctor_set(v___x_3458_, 1, v_k_2833_);
lean_ctor_set(v___x_3458_, 0, v___x_3327_);
v___x_3469_ = v___x_3458_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_l_3418_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_l_3418_);
v___x_3469_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
lean_object* v___x_3471_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v___x_3469_);
lean_ctor_set(v___x_2838_, 3, v___x_3467_);
lean_ctor_set(v___x_2838_, 2, v_v_3461_);
lean_ctor_set(v___x_2838_, 1, v_k_3460_);
lean_ctor_set(v___x_2838_, 0, v___x_3465_);
v___x_3471_ = v___x_2838_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_k_3460_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_v_3461_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v___x_3467_);
lean_ctor_set(v_reuseFailAlloc_3472_, 4, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
}
else
{
lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3483_ = lean_unsigned_to_nat(2u);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_r_3454_);
lean_ctor_set(v___x_2838_, 0, v___x_3483_);
v___x_3485_ = v___x_2838_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_r_3454_);
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
else
{
lean_object* v___x_3488_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 4, v_l_2835_);
lean_ctor_set(v___x_2838_, 0, v___x_3327_);
v___x_3488_ = v___x_2838_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3327_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_k_2833_);
lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_v_2834_);
lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_l_2835_);
lean_ctor_set(v_reuseFailAlloc_3489_, 4, v_l_2835_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
}
}
else
{
return v_t_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3492_, lean_object* v_t_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3492_, v_t_3493_);
lean_dec(v_k_3492_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3495_, lean_object* v_ps_3496_){
_start:
{
lean_object* v_importedEntries_3497_; lean_object* v_state_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3506_; 
v_importedEntries_3497_ = lean_ctor_get(v_ps_3496_, 0);
v_state_3498_ = lean_ctor_get(v_ps_3496_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_ps_3496_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3500_ = v_ps_3496_;
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_state_3498_);
lean_inc(v_importedEntries_3497_);
lean_dec(v_ps_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3495_, v_state_3498_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3502_);
v___x_3504_ = v___x_3500_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_importedEntries_3497_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3507_, lean_object* v_ps_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3507_, v_ps_3508_);
lean_dec(v_declName_3507_);
return v_res_3509_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___f_3553_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___x_3576_; lean_object* v_env_3577_; lean_object* v___x_3578_; 
lean_inc(v_declName_3513_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3553_, 0, v_declName_3513_);
v___x_3576_ = lean_st_ref_get(v___y_3519_);
v_env_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc_ref(v_env_3577_);
lean_dec(v___x_3576_);
v___x_3578_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3577_, v_declName_3513_);
lean_dec_ref(v_env_3577_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_dec(v_declName_3513_);
v___y_3555_ = v___y_3517_;
v___y_3556_ = v___y_3519_;
goto v___jp_3554_;
}
else
{
uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
lean_dec_ref_known(v___x_3578_, 1);
lean_dec_ref(v___f_3553_);
v___x_3579_ = 0;
v___x_3580_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3581_ = l_Lean_MessageData_ofConstName(v_declName_3513_, v___x_3579_);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v___x_3583_);
v___x_3585_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3584_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
return v___x_3585_;
}
v___jp_3521_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v_mctx_3537_; lean_object* v_zetaDeltaFVarIds_3538_; lean_object* v_postponed_3539_; lean_object* v_diag_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3551_; 
v___x_3533_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_3534_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3534_, 0, v___y_3532_);
lean_ctor_set(v___x_3534_, 1, v___y_3527_);
lean_ctor_set(v___x_3534_, 2, v___y_3524_);
lean_ctor_set(v___x_3534_, 3, v___y_3530_);
lean_ctor_set(v___x_3534_, 4, v___y_3526_);
lean_ctor_set(v___x_3534_, 5, v___x_3533_);
lean_ctor_set(v___x_3534_, 6, v___y_3525_);
lean_ctor_set(v___x_3534_, 7, v___y_3529_);
lean_ctor_set(v___x_3534_, 8, v___y_3522_);
lean_ctor_set(v___x_3534_, 9, v___y_3531_);
v___x_3535_ = lean_st_ref_put(v___y_3528_, v___x_3534_);
v___x_3536_ = lean_st_ref_take(v___y_3523_);
v_mctx_3537_ = lean_ctor_get(v___x_3536_, 0);
v_zetaDeltaFVarIds_3538_ = lean_ctor_get(v___x_3536_, 2);
v_postponed_3539_ = lean_ctor_get(v___x_3536_, 3);
v_diag_3540_ = lean_ctor_get(v___x_3536_, 4);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v___x_3536_, 1);
lean_dec(v_unused_3552_);
v___x_3542_ = v___x_3536_;
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_diag_3540_);
lean_inc(v_postponed_3539_);
lean_inc(v_zetaDeltaFVarIds_3538_);
lean_inc(v_mctx_3537_);
lean_dec(v___x_3536_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3547_; 
v___x_3544_ = lean_box(0);
v___x_3545_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3545_);
v___x_3547_ = v___x_3542_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_mctx_3537_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_zetaDeltaFVarIds_3538_);
lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_postponed_3539_);
lean_ctor_set(v_reuseFailAlloc_3550_, 4, v_diag_3540_);
v___x_3547_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3548_ = lean_st_ref_put(v___y_3523_, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3544_);
return v___x_3549_;
}
}
}
v___jp_3554_:
{
lean_object* v___x_3557_; lean_object* v_env_3558_; lean_object* v_nextMacroScope_3559_; lean_object* v_ngen_3560_; lean_object* v_auxDeclNGen_3561_; lean_object* v_traceState_3562_; lean_object* v_recordedDeps_3563_; lean_object* v_messages_3564_; lean_object* v_infoState_3565_; lean_object* v_snapshotTasks_3566_; lean_object* v___x_3567_; lean_object* v_toEnvExtension_3568_; uint8_t v_logWrites_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3557_ = lean_st_ref_take(v___y_3556_);
v_env_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc_ref(v_env_3558_);
v_nextMacroScope_3559_ = lean_ctor_get(v___x_3557_, 1);
lean_inc(v_nextMacroScope_3559_);
v_ngen_3560_ = lean_ctor_get(v___x_3557_, 2);
lean_inc_ref(v_ngen_3560_);
v_auxDeclNGen_3561_ = lean_ctor_get(v___x_3557_, 3);
lean_inc_ref(v_auxDeclNGen_3561_);
v_traceState_3562_ = lean_ctor_get(v___x_3557_, 4);
lean_inc_ref(v_traceState_3562_);
v_recordedDeps_3563_ = lean_ctor_get(v___x_3557_, 6);
lean_inc_ref(v_recordedDeps_3563_);
v_messages_3564_ = lean_ctor_get(v___x_3557_, 7);
lean_inc_ref(v_messages_3564_);
v_infoState_3565_ = lean_ctor_get(v___x_3557_, 8);
lean_inc_ref(v_infoState_3565_);
v_snapshotTasks_3566_ = lean_ctor_get(v___x_3557_, 9);
lean_inc_ref(v_snapshotTasks_3566_);
lean_dec(v___x_3557_);
v___x_3567_ = l_Lean_docStringExt;
v_toEnvExtension_3568_ = lean_ctor_get(v___x_3567_, 0);
v_logWrites_3569_ = lean_ctor_get_uint8(v_toEnvExtension_3568_, sizeof(void*)*6);
v___x_3570_ = lean_box(2);
v___x_3571_ = lean_box(0);
v___x_3572_ = 1;
if (v_logWrites_3569_ == 0)
{
lean_object* v___x_3573_; 
lean_inc_ref(v_toEnvExtension_3568_);
v___x_3573_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3568_, v_env_3558_, v___f_3553_, v___x_3570_, v___x_3571_, v___x_3572_);
v___y_3522_ = v_infoState_3565_;
v___y_3523_ = v___y_3555_;
v___y_3524_ = v_ngen_3560_;
v___y_3525_ = v_recordedDeps_3563_;
v___y_3526_ = v_traceState_3562_;
v___y_3527_ = v_nextMacroScope_3559_;
v___y_3528_ = v___y_3556_;
v___y_3529_ = v_messages_3564_;
v___y_3530_ = v_auxDeclNGen_3561_;
v___y_3531_ = v_snapshotTasks_3566_;
v___y_3532_ = v___x_3573_;
goto v___jp_3521_;
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_inc_ref_n(v_toEnvExtension_3568_, 2);
v___x_3574_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3568_, v_env_3558_);
lean_dec_ref(v_env_3558_);
v___x_3575_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3568_, v___x_3574_, v___f_3553_, v___x_3570_, v___x_3571_, v___x_3572_);
v___y_3522_ = v_infoState_3565_;
v___y_3523_ = v___y_3555_;
v___y_3524_ = v_ngen_3560_;
v___y_3525_ = v_recordedDeps_3563_;
v___y_3526_ = v_traceState_3562_;
v___y_3527_ = v_nextMacroScope_3559_;
v___y_3528_ = v___y_3556_;
v___y_3529_ = v_messages_3564_;
v___y_3530_ = v_auxDeclNGen_3561_;
v___y_3531_ = v_snapshotTasks_3566_;
v___y_3532_ = v___x_3575_;
goto v___jp_3521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
return v_res_3594_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3603_ = l_Lean_stringToMessageData(v___x_3602_);
return v___x_3603_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3606_ = l_Lean_stringToMessageData(v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v_env_3616_; lean_object* v_ref_3617_; uint8_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3615_ = lean_st_ref_get(v_a_3613_);
v_env_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc_ref(v_env_3616_);
lean_dec(v___x_3615_);
v_ref_3617_ = lean_ctor_get(v_a_3612_, 2);
v___x_3618_ = 1;
lean_inc(v_declName_3607_);
v___x_3619_ = l_Lean_findInternalDocString_x3f(v_env_3616_, v_declName_3607_, v___x_3618_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3619_, 1);
if (lean_obj_tag(v_a_3620_) == 1)
{
lean_object* v_val_3621_; 
v_val_3621_ = lean_ctor_get(v_a_3620_, 0);
lean_inc(v_val_3621_);
lean_dec_ref_known(v_a_3620_, 1);
if (lean_obj_tag(v_val_3621_) == 0)
{
lean_object* v_val_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3643_; 
v_val_3622_ = lean_ctor_get(v_val_3621_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_val_3621_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3624_ = v_val_3621_;
v_isShared_3625_ = v_isSharedCheck_3643_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_val_3622_);
lean_dec(v_val_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3643_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_removeBuiltinDocString(v_declName_3607_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref_known(v___x_3626_, 1);
lean_del_object(v___x_3624_);
lean_inc(v_declName_3607_);
v___x_3627_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v___x_3628_; 
lean_dec_ref_known(v___x_3627_, 1);
v___x_3628_ = l_Lean_addVersoDocStringFromString(v_declName_3607_, v_val_3622_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
return v___x_3628_;
}
else
{
lean_dec(v_val_3622_);
lean_dec(v_declName_3607_);
return v___x_3627_;
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_val_3622_);
lean_dec(v_declName_3607_);
v_a_3629_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3631_ = v___x_3626_;
v_isShared_3632_ = v_isSharedCheck_3642_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3626_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3642_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
v___x_3633_ = lean_io_error_to_string(v_a_3629_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set_tag(v___x_3624_, 3);
lean_ctor_set(v___x_3624_, 0, v___x_3633_);
v___x_3635_ = v___x_3624_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3639_; 
v___x_3636_ = l_Lean_MessageData_ofFormat(v___x_3635_);
lean_inc(v_ref_3617_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_ref_3617_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3637_);
v___x_3639_ = v___x_3631_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
}
else
{
lean_object* v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
lean_dec(v_val_3621_);
v___x_3644_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3645_ = 0;
v___x_3646_ = l_Lean_MessageData_ofConstName(v_declName_3607_, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3644_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3649_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
return v___x_3650_;
}
}
else
{
lean_object* v___x_3651_; uint8_t v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec(v_a_3620_);
v___x_3651_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3652_ = 0;
v___x_3653_ = l_Lean_MessageData_ofConstName(v_declName_3607_, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3651_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3656_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
return v___x_3657_;
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3669_; 
lean_dec(v_declName_3607_);
v_a_3658_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3660_ = v___x_3619_;
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3619_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3662_ = lean_io_error_to_string(v_a_3658_);
v___x_3663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
v___x_3664_ = l_Lean_MessageData_ofFormat(v___x_3663_);
lean_inc(v_ref_3617_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_ref_3617_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3665_);
v___x_3667_ = v___x_3660_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_makeDocStringVerso(v_declName_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3679_, lean_object* v_k_3680_, lean_object* v_t_3681_, lean_object* v_h_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3680_, v_t_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3684_, lean_object* v_k_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3684_, v_k_3685_, v_t_3686_, v_h_3687_);
lean_dec(v_k_3685_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3689_, lean_object* v_binders_3690_, lean_object* v_docComment_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
uint8_t v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = l_Lean_isVersoDocComment(v_docComment_3691_);
v___x_3700_ = l_Lean_addDocStringOf(v___x_3699_, v_declName_3689_, v_binders_3690_, v_docComment_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3701_, lean_object* v_binders_3702_, lean_object* v_docComment_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_addDocString(v_declName_3701_, v_binders_3702_, v_docComment_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3712_, lean_object* v_binders_3713_, lean_object* v_docString_x3f_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3714_) == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec(v_binders_3713_);
lean_dec(v_declName_3712_);
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
else
{
lean_object* v_val_3724_; lean_object* v___x_3725_; 
v_val_3724_ = lean_ctor_get(v_docString_x3f_3714_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v_docString_x3f_3714_, 1);
v___x_3725_ = l_Lean_addDocString(v_declName_3712_, v_binders_3713_, v_val_3724_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
return v___x_3725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3726_, lean_object* v_binders_3727_, lean_object* v_docString_x3f_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_Lean_addDocString_x27(v_declName_3726_, v_binders_3727_, v_docString_x3f_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; lean_object* v_nextMacroScope_3742_; lean_object* v_ngen_3743_; lean_object* v_auxDeclNGen_3744_; lean_object* v_traceState_3745_; lean_object* v_recordedDeps_3746_; lean_object* v_messages_3747_; lean_object* v_infoState_3748_; lean_object* v_snapshotTasks_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3775_; 
v___x_3741_ = lean_st_ref_take(v___y_3739_);
v_nextMacroScope_3742_ = lean_ctor_get(v___x_3741_, 1);
v_ngen_3743_ = lean_ctor_get(v___x_3741_, 2);
v_auxDeclNGen_3744_ = lean_ctor_get(v___x_3741_, 3);
v_traceState_3745_ = lean_ctor_get(v___x_3741_, 4);
v_recordedDeps_3746_ = lean_ctor_get(v___x_3741_, 6);
v_messages_3747_ = lean_ctor_get(v___x_3741_, 7);
v_infoState_3748_ = lean_ctor_get(v___x_3741_, 8);
v_snapshotTasks_3749_ = lean_ctor_get(v___x_3741_, 9);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; lean_object* v_unused_3777_; 
v_unused_3776_ = lean_ctor_get(v___x_3741_, 5);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v___x_3741_, 0);
lean_dec(v_unused_3777_);
v___x_3751_ = v___x_3741_;
v_isShared_3752_ = v_isSharedCheck_3775_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_snapshotTasks_3749_);
lean_inc(v_infoState_3748_);
lean_inc(v_messages_3747_);
lean_inc(v_recordedDeps_3746_);
lean_inc(v_traceState_3745_);
lean_inc(v_auxDeclNGen_3744_);
lean_inc(v_ngen_3743_);
lean_inc(v_nextMacroScope_3742_);
lean_dec(v___x_3741_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3775_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3753_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 5, v___x_3753_);
lean_ctor_set(v___x_3751_, 0, v_env_3737_);
v___x_3755_ = v___x_3751_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_env_3737_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_nextMacroScope_3742_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_ngen_3743_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_auxDeclNGen_3744_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v_traceState_3745_);
lean_ctor_set(v_reuseFailAlloc_3774_, 5, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3774_, 6, v_recordedDeps_3746_);
lean_ctor_set(v_reuseFailAlloc_3774_, 7, v_messages_3747_);
lean_ctor_set(v_reuseFailAlloc_3774_, 8, v_infoState_3748_);
lean_ctor_set(v_reuseFailAlloc_3774_, 9, v_snapshotTasks_3749_);
v___x_3755_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v_mctx_3758_; lean_object* v_zetaDeltaFVarIds_3759_; lean_object* v_postponed_3760_; lean_object* v_diag_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3772_; 
v___x_3756_ = lean_st_ref_put(v___y_3739_, v___x_3755_);
v___x_3757_ = lean_st_ref_take(v___y_3738_);
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
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3765_ = lean_box(0);
v___x_3766_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__5);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_mctx_3758_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_zetaDeltaFVarIds_3759_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_postponed_3760_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v_diag_3761_);
v___x_3768_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_st_ref_put(v___y_3738_, v___x_3768_);
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3765_);
return v___x_3770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec(v___y_3779_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3783_, uint8_t v___x_3784_, lean_object* v_as_3785_, size_t v_i_3786_, size_t v_stop_3787_, lean_object* v_b_3788_){
_start:
{
lean_object* v___y_3790_; uint8_t v___x_3794_; 
v___x_3794_ = lean_usize_dec_eq(v_i_3786_, v_stop_3787_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v_index_3796_; lean_object* v_sourceString_3797_; lean_object* v_imports_3798_; lean_object* v_currNamespace_3799_; lean_object* v_openDecls_3800_; lean_object* v_options_3801_; lean_object* v_check_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3820_; 
v___x_3795_ = lean_array_uget(v_as_3785_, v_i_3786_);
v_index_3796_ = lean_ctor_get(v___x_3795_, 1);
v_sourceString_3797_ = lean_ctor_get(v___x_3795_, 2);
v_imports_3798_ = lean_ctor_get(v___x_3795_, 3);
v_currNamespace_3799_ = lean_ctor_get(v___x_3795_, 4);
v_openDecls_3800_ = lean_ctor_get(v___x_3795_, 5);
v_options_3801_ = lean_ctor_get(v___x_3795_, 6);
v_check_3802_ = lean_ctor_get(v___x_3795_, 7);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3795_, 0);
lean_dec(v_unused_3821_);
v___x_3804_ = v___x_3795_;
v_isShared_3805_ = v_isSharedCheck_3820_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_check_3802_);
lean_inc(v_options_3801_);
lean_inc(v_openDecls_3800_);
lean_inc(v_currNamespace_3799_);
lean_inc(v_imports_3798_);
lean_inc(v_sourceString_3797_);
lean_inc(v_index_3796_);
lean_dec(v___x_3795_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3820_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3806_; lean_object* v_toEnvExtension_3807_; lean_object* v_addEntryFn_3808_; lean_object* v_asyncMode_3809_; uint8_t v_logWrites_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3806_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3807_ = lean_ctor_get(v___x_3806_, 0);
v_addEntryFn_3808_ = lean_ctor_get(v___x_3806_, 3);
v_asyncMode_3809_ = lean_ctor_get(v_toEnvExtension_3807_, 2);
v_logWrites_3810_ = lean_ctor_get_uint8(v_toEnvExtension_3807_, sizeof(void*)*6);
lean_inc(v_n_3783_);
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_n_3783_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3811_);
v___x_3813_ = v___x_3804_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_index_3796_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_sourceString_3797_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_imports_3798_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_currNamespace_3799_);
lean_ctor_set(v_reuseFailAlloc_3819_, 5, v_openDecls_3800_);
lean_ctor_set(v_reuseFailAlloc_3819_, 6, v_options_3801_);
lean_ctor_set(v_reuseFailAlloc_3819_, 7, v_check_3802_);
v___x_3813_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___f_3814_; lean_object* v___x_3815_; 
lean_inc(v_addEntryFn_3808_);
v___f_3814_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_3814_, 0, v_addEntryFn_3808_);
lean_closure_set(v___f_3814_, 1, v___x_3813_);
v___x_3815_ = lean_box(0);
if (v_logWrites_3810_ == 0)
{
lean_object* v___x_3816_; 
lean_inc_ref(v_toEnvExtension_3807_);
v___x_3816_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3807_, v_b_3788_, v___f_3814_, v_asyncMode_3809_, v___x_3815_, v___x_3784_);
v___y_3790_ = v___x_3816_;
goto v___jp_3789_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_inc_ref_n(v_toEnvExtension_3807_, 2);
v___x_3817_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3807_, v_b_3788_);
lean_dec_ref(v_b_3788_);
v___x_3818_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3807_, v___x_3817_, v___f_3814_, v_asyncMode_3809_, v___x_3815_, v___x_3784_);
v___y_3790_ = v___x_3818_;
goto v___jp_3789_;
}
}
}
}
else
{
lean_dec(v_n_3783_);
return v_b_3788_;
}
v___jp_3789_:
{
size_t v___x_3791_; size_t v___x_3792_; 
v___x_3791_ = ((size_t)1ULL);
v___x_3792_ = lean_usize_add(v_i_3786_, v___x_3791_);
v_i_3786_ = v___x_3792_;
v_b_3788_ = v___y_3790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3822_, lean_object* v___x_3823_, lean_object* v_as_3824_, lean_object* v_i_3825_, lean_object* v_stop_3826_, lean_object* v_b_3827_){
_start:
{
uint8_t v___x_1426__boxed_3828_; size_t v_i_boxed_3829_; size_t v_stop_boxed_3830_; lean_object* v_res_3831_; 
v___x_1426__boxed_3828_ = lean_unbox(v___x_3823_);
v_i_boxed_3829_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_stop_boxed_3830_ = lean_unbox_usize(v_stop_3826_);
lean_dec(v_stop_3826_);
v_res_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3822_, v___x_1426__boxed_3828_, v_as_3824_, v_i_boxed_3829_, v_stop_boxed_3830_, v_b_3827_);
lean_dec_ref(v_as_3824_);
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3832_, lean_object* v_deferred_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v_env_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3841_ = lean_st_ref_get(v___y_3839_);
v_env_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc_ref(v_env_3842_);
lean_dec(v___x_3841_);
v___x_3843_ = l_Lean_getMainModuleDoc(v_env_3842_);
v___x_3844_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3843_);
lean_dec_ref(v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec_ref(v_docs_3832_);
v___x_3845_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3846_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3845_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; lean_object* v_env_3848_; lean_object* v___x_3849_; lean_object* v_size_3850_; lean_object* v___x_3851_; lean_object* v_env_3852_; lean_object* v___x_3853_; 
v___x_3847_ = lean_st_ref_get(v___y_3839_);
v_env_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc_ref(v_env_3848_);
lean_dec(v___x_3847_);
v___x_3849_ = l_Lean_getMainVersoModuleDocs(v_env_3848_);
v_size_3850_ = lean_ctor_get(v___x_3849_, 2);
lean_inc(v_size_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = lean_st_ref_get(v___y_3839_);
v_env_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc_ref(v_env_3852_);
lean_dec(v___x_3851_);
v___x_3853_ = l_Lean_addVersoModuleDocSnippet(v_env_3852_, v_docs_3832_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec(v_size_3850_);
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3855_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_3856_ = l_Lean_stringToMessageData(v_a_3854_);
v___x_3857_ = l_Lean_indentD(v___x_3856_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3855_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3858_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3859_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_a_3860_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3861_ = lean_unsigned_to_nat(0u);
v___x_3862_ = lean_array_get_size(v_deferred_3833_);
v___x_3863_ = lean_nat_dec_lt(v___x_3861_, v___x_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; 
lean_dec(v_size_3850_);
v___x_3864_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3860_, v___y_3837_, v___y_3839_);
return v___x_3864_;
}
else
{
size_t v___x_3865_; size_t v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3865_ = ((size_t)0ULL);
v___x_3866_ = lean_usize_of_nat(v___x_3862_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3850_, v___x_3844_, v_deferred_3833_, v___x_3865_, v___x_3866_, v_a_3860_);
v___x_3868_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3867_, v___y_3837_, v___y_3839_);
return v___x_3868_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3869_, lean_object* v_deferred_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3869_, v_deferred_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v_deferred_3870_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3879_, lean_object* v_doc_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_versoModDocString(v_range_3879_, v_doc_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v_fst_3890_; lean_object* v_snd_3891_; lean_object* v___x_3892_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
v_fst_3890_ = lean_ctor_get(v_a_3889_, 0);
lean_inc(v_fst_3890_);
v_snd_3891_ = lean_ctor_get(v_a_3889_, 1);
lean_inc(v_snd_3891_);
lean_dec(v_a_3889_);
v___x_3892_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3890_, v_snd_3891_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_snd_3891_);
return v___x_3892_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_a_3893_ = lean_ctor_get(v___x_3888_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3888_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3888_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3901_, lean_object* v_doc_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_addVersoModDocString(v_range_3901_, v_doc_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_doc_3902_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3911_, v___y_3915_, v___y_3917_);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
return v_res_3928_;
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
