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
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__0));
v___x_279_ = l_Lean_stringToMessageData(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__1);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange(lean_object* v_docComment_282_){
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
v___x_284_ = lean_obj_once(&l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2, &l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2_once, _init_l___private_Lean_DocString_Add_0__Lean_docStringRange___closed__2);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_docStringRange___boxed(lean_object* v_docComment_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_316_);
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
v___x_594_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_581_);
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
lean_object* v_toCold_683_; lean_object* v_val_684_; lean_object* v_currRecDepth_685_; lean_object* v_ref_686_; uint16_t v_optionFlags_687_; uint8_t v_suppressElabErrors_688_; uint8_t v_isRecordingDeps_689_; lean_object* v_fileName_690_; lean_object* v_options_691_; lean_object* v_maxRecDepth_692_; lean_object* v_currNamespace_693_; lean_object* v_openDecls_694_; lean_object* v_initHeartbeats_695_; lean_object* v_maxHeartbeats_696_; lean_object* v_quotContext_697_; lean_object* v_currMacroScope_698_; lean_object* v_cancelTk_x3f_699_; lean_object* v_inheritedTraceOptions_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_toCold_683_ = lean_ctor_get(v___y_679_, 0);
v_val_684_ = lean_ctor_get(v_fileMap_x3f_670_, 0);
v_currRecDepth_685_ = lean_ctor_get(v___y_679_, 1);
v_ref_686_ = lean_ctor_get(v___y_679_, 2);
v_optionFlags_687_ = lean_ctor_get_uint16(v___y_679_, sizeof(void*)*3);
v_suppressElabErrors_688_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*3 + 2);
v_isRecordingDeps_689_ = lean_ctor_get_uint8(v___y_679_, sizeof(void*)*3 + 3);
v_fileName_690_ = lean_ctor_get(v_toCold_683_, 0);
v_options_691_ = lean_ctor_get(v_toCold_683_, 2);
v_maxRecDepth_692_ = lean_ctor_get(v_toCold_683_, 3);
v_currNamespace_693_ = lean_ctor_get(v_toCold_683_, 4);
v_openDecls_694_ = lean_ctor_get(v_toCold_683_, 5);
v_initHeartbeats_695_ = lean_ctor_get(v_toCold_683_, 6);
v_maxHeartbeats_696_ = lean_ctor_get(v_toCold_683_, 7);
v_quotContext_697_ = lean_ctor_get(v_toCold_683_, 8);
v_currMacroScope_698_ = lean_ctor_get(v_toCold_683_, 9);
v_cancelTk_x3f_699_ = lean_ctor_get(v_toCold_683_, 10);
v_inheritedTraceOptions_700_ = lean_ctor_get(v_toCold_683_, 11);
lean_inc_ref(v_inheritedTraceOptions_700_);
lean_inc(v_cancelTk_x3f_699_);
lean_inc(v_currMacroScope_698_);
lean_inc(v_quotContext_697_);
lean_inc(v_maxHeartbeats_696_);
lean_inc(v_initHeartbeats_695_);
lean_inc(v_openDecls_694_);
lean_inc(v_currNamespace_693_);
lean_inc(v_maxRecDepth_692_);
lean_inc_ref(v_options_691_);
lean_inc(v_val_684_);
lean_inc_ref(v_fileName_690_);
v___x_701_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_701_, 0, v_fileName_690_);
lean_ctor_set(v___x_701_, 1, v_val_684_);
lean_ctor_set(v___x_701_, 2, v_options_691_);
lean_ctor_set(v___x_701_, 3, v_maxRecDepth_692_);
lean_ctor_set(v___x_701_, 4, v_currNamespace_693_);
lean_ctor_set(v___x_701_, 5, v_openDecls_694_);
lean_ctor_set(v___x_701_, 6, v_initHeartbeats_695_);
lean_ctor_set(v___x_701_, 7, v_maxHeartbeats_696_);
lean_ctor_set(v___x_701_, 8, v_quotContext_697_);
lean_ctor_set(v___x_701_, 9, v_currMacroScope_698_);
lean_ctor_set(v___x_701_, 10, v_cancelTk_x3f_699_);
lean_ctor_set(v___x_701_, 11, v_inheritedTraceOptions_700_);
lean_inc(v_ref_686_);
lean_inc(v_currRecDepth_685_);
v___x_702_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_currRecDepth_685_);
lean_ctor_set(v___x_702_, 2, v_ref_686_);
lean_ctor_set_uint16(v___x_702_, sizeof(void*)*3, v_optionFlags_687_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*3 + 2, v_suppressElabErrors_688_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*3 + 3, v_isRecordingDeps_689_);
v___x_703_ = l_Lean_Doc_DocM_exec___redArg(v_declName_671_, v_binders_672_, v___x_673_, v___x_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___x_702_, v___y_680_);
lean_dec_ref_known(v___x_702_, 3);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed(lean_object* v_fileMap_x3f_704_, lean_object* v_declName_705_, lean_object* v_binders_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___x_9836__boxed_716_; lean_object* v_res_717_; 
v___x_9836__boxed_716_ = lean_unbox(v___x_708_);
v_res_717_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0(v_fileMap_x3f_704_, v_declName_705_, v_binders_706_, v___x_707_, v___x_9836__boxed_716_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_fileMap_x3f_704_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(size_t v_sz_718_, size_t v_i_719_, lean_object* v_bs_720_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_721_ == 0)
{
return v_bs_720_;
}
else
{
lean_object* v_v_722_; lean_object* v___x_723_; lean_object* v_bs_x27_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v_v_722_ = lean_array_uget(v_bs_720_, v_i_719_);
v___x_723_ = lean_unsigned_to_nat(0u);
v_bs_x27_724_ = lean_array_uset(v_bs_720_, v_i_719_, v___x_723_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_719_, v___x_725_);
v___x_727_ = lean_array_uset(v_bs_x27_724_, v_i_719_, v_v_722_);
v_i_719_ = v___x_726_;
v_bs_720_ = v___x_727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0___boxed(lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_bs_731_){
_start:
{
size_t v_sz_boxed_732_; size_t v_i_boxed_733_; lean_object* v_res_734_; 
v_sz_boxed_732_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_733_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_boxed_732_, v_i_boxed_733_, v_bs_731_);
return v_res_734_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(lean_object* v_opts_735_, lean_object* v_opt_736_){
_start:
{
lean_object* v_name_737_; lean_object* v_defValue_738_; lean_object* v_map_739_; lean_object* v___x_740_; 
v_name_737_ = lean_ctor_get(v_opt_736_, 0);
v_defValue_738_ = lean_ctor_get(v_opt_736_, 1);
v_map_739_ = lean_ctor_get(v_opts_735_, 0);
v___x_740_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_739_, v_name_737_);
if (lean_obj_tag(v___x_740_) == 0)
{
uint8_t v___x_741_; 
v___x_741_ = lean_unbox(v_defValue_738_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; 
v_val_742_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_740_, 1);
if (lean_obj_tag(v_val_742_) == 1)
{
uint8_t v_v_743_; 
v_v_743_ = lean_ctor_get_uint8(v_val_742_, 0);
lean_dec_ref_known(v_val_742_, 0);
return v_v_743_;
}
else
{
uint8_t v___x_744_; 
lean_dec(v_val_742_);
v___x_744_ = lean_unbox(v_defValue_738_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4___boxed(lean_object* v_opts_745_, lean_object* v_opt_746_){
_start:
{
uint8_t v_res_747_; lean_object* v_r_748_; 
v_res_747_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v_opts_745_, v_opt_746_);
lean_dec_ref(v_opt_746_);
lean_dec_ref(v_opts_745_);
v_r_748_ = lean_box(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(lean_object* v_msgData_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_755_; lean_object* v_env_756_; uint8_t v___x_757_; lean_object* v_env_758_; lean_object* v___x_759_; lean_object* v_toCold_760_; lean_object* v_mctx_761_; lean_object* v_lctx_762_; lean_object* v_options_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_755_ = lean_st_ref_get(v___y_753_);
v_env_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc_ref(v_env_756_);
lean_dec(v___x_755_);
v___x_757_ = 0;
v_env_758_ = l_Lean_Environment_setRecordingDeps(v_env_756_, v___x_757_);
v___x_759_ = lean_st_ref_get(v___y_751_);
v_toCold_760_ = lean_ctor_get(v___y_752_, 0);
v_mctx_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc_ref(v_mctx_761_);
lean_dec(v___x_759_);
v_lctx_762_ = lean_ctor_get(v___y_750_, 2);
v_options_763_ = lean_ctor_get(v_toCold_760_, 2);
lean_inc_ref(v_options_763_);
lean_inc_ref(v_lctx_762_);
v___x_764_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_764_, 0, v_env_758_);
lean_ctor_set(v___x_764_, 1, v_mctx_761_);
lean_ctor_set(v___x_764_, 2, v_lctx_762_);
lean_ctor_set(v___x_764_, 3, v_options_763_);
v___x_765_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v_msgData_749_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3___boxed(lean_object* v_msgData_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msgData_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(uint8_t v_suppressElabErrors_774_, uint8_t v___y_775_, lean_object* v_x_776_){
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
return v_suppressElabErrors_774_;
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
return v_suppressElabErrors_774_;
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
return v_suppressElabErrors_774_;
}
}
}
}
else
{
return v___y_775_;
}
}
default: 
{
return v___y_775_;
}
}
}
case 0:
{
lean_object* v_str_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_str_799_ = lean_ctor_get(v_x_776_, 1);
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_parseVersoDocStringAt_spec__0___lam__0___closed__7));
v___x_801_ = lean_string_dec_eq(v_str_799_, v___x_800_);
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
return v_suppressElabErrors_774_;
}
}
default: 
{
return v___y_775_;
}
}
}
else
{
return v___y_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_802_, lean_object* v___y_803_, lean_object* v_x_804_){
_start:
{
uint8_t v_suppressElabErrors_boxed_805_; uint8_t v___y_9929__boxed_806_; uint8_t v_res_807_; lean_object* v_r_808_; 
v_suppressElabErrors_boxed_805_ = lean_unbox(v_suppressElabErrors_802_);
v___y_9929__boxed_806_ = lean_unbox(v___y_803_);
v_res_807_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0(v_suppressElabErrors_boxed_805_, v___y_9929__boxed_806_, v_x_804_);
lean_dec(v_x_804_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(lean_object* v_ref_809_, lean_object* v_msgData_810_, uint8_t v_severity_811_, uint8_t v_isSilent_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; uint8_t v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v_toCold_826_; lean_object* v___y_827_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; uint8_t v___y_859_; uint8_t v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_883_; uint8_t v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_887_; uint8_t v___y_888_; lean_object* v___y_889_; uint8_t v___y_893_; uint8_t v___y_894_; uint8_t v___y_895_; uint8_t v___x_906_; uint8_t v___y_908_; uint8_t v___y_909_; uint8_t v___y_910_; uint8_t v___y_912_; uint8_t v___x_920_; 
v___x_906_ = 2;
v___x_920_ = l_Lean_instBEqMessageSeverity_beq(v_severity_811_, v___x_906_);
if (v___x_920_ == 0)
{
v___y_912_ = v___x_920_;
goto v___jp_911_;
}
else
{
uint8_t v___x_921_; 
lean_inc_ref(v_msgData_810_);
v___x_921_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_810_);
v___y_912_ = v___x_921_;
goto v___jp_911_;
}
v___jp_818_:
{
lean_object* v_currNamespace_828_; lean_object* v_openDecls_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_env_834_; lean_object* v_nextMacroScope_835_; lean_object* v_ngen_836_; lean_object* v_auxDeclNGen_837_; lean_object* v_traceState_838_; lean_object* v_cache_839_; lean_object* v_recordedDeps_840_; lean_object* v_messages_841_; lean_object* v_infoState_842_; lean_object* v_snapshotTasks_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_854_; 
v_currNamespace_828_ = lean_ctor_get(v_toCold_826_, 4);
v_openDecls_829_ = lean_ctor_get(v_toCold_826_, 5);
lean_inc(v_openDecls_829_);
lean_inc(v_currNamespace_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_currNamespace_828_);
lean_ctor_set(v___x_830_, 1, v_openDecls_829_);
v___x_831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___y_821_);
lean_inc_ref(v___y_825_);
lean_inc_ref(v___y_820_);
v___x_832_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_832_, 0, v___y_820_);
lean_ctor_set(v___x_832_, 1, v___y_819_);
lean_ctor_set(v___x_832_, 2, v___y_822_);
lean_ctor_set(v___x_832_, 3, v___y_825_);
lean_ctor_set(v___x_832_, 4, v___x_831_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*5, v___y_824_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*5 + 1, v___y_823_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*5 + 2, v_isSilent_812_);
v___x_833_ = lean_st_ref_take(v___y_827_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
v_nextMacroScope_835_ = lean_ctor_get(v___x_833_, 1);
v_ngen_836_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_837_ = lean_ctor_get(v___x_833_, 3);
v_traceState_838_ = lean_ctor_get(v___x_833_, 4);
v_cache_839_ = lean_ctor_get(v___x_833_, 5);
v_recordedDeps_840_ = lean_ctor_get(v___x_833_, 6);
v_messages_841_ = lean_ctor_get(v___x_833_, 7);
v_infoState_842_ = lean_ctor_get(v___x_833_, 8);
v_snapshotTasks_843_ = lean_ctor_get(v___x_833_, 9);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_854_ == 0)
{
v___x_845_ = v___x_833_;
v_isShared_846_ = v_isSharedCheck_854_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_snapshotTasks_843_);
lean_inc(v_infoState_842_);
lean_inc(v_messages_841_);
lean_inc(v_recordedDeps_840_);
lean_inc(v_cache_839_);
lean_inc(v_traceState_838_);
lean_inc(v_auxDeclNGen_837_);
lean_inc(v_ngen_836_);
lean_inc(v_nextMacroScope_835_);
lean_inc(v_env_834_);
lean_dec(v___x_833_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_854_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_MessageLog_add(v___x_832_, v_messages_841_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 7, v___x_848_);
v___x_850_ = v___x_845_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_env_834_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_nextMacroScope_835_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_ngen_836_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_auxDeclNGen_837_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v_traceState_838_);
lean_ctor_set(v_reuseFailAlloc_853_, 5, v_cache_839_);
lean_ctor_set(v_reuseFailAlloc_853_, 6, v_recordedDeps_840_);
lean_ctor_set(v_reuseFailAlloc_853_, 7, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_853_, 8, v_infoState_842_);
lean_ctor_set(v_reuseFailAlloc_853_, 9, v_snapshotTasks_843_);
v___x_850_ = v_reuseFailAlloc_853_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_st_ref_put(v___y_827_, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_847_);
return v___x_852_;
}
}
}
v___jp_855_:
{
lean_object* v_fileName_864_; lean_object* v_fileMap_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_881_; 
v_fileName_864_ = lean_ctor_get(v___y_862_, 0);
v_fileMap_865_ = lean_ctor_get(v___y_862_, 1);
v___x_866_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_810_);
v___x_867_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v___x_866_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_881_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc_ref_n(v_fileMap_865_, 2);
v___x_872_ = l_Lean_FileMap_toPosition(v_fileMap_865_, v___y_858_);
lean_dec(v___y_858_);
v___x_873_ = l_Lean_FileMap_toPosition(v_fileMap_865_, v___y_863_);
lean_dec(v___y_863_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
v___x_875_ = ((lean_object*)(l___private_Lean_DocString_Add_0__Lean_mkVersoParseMessage___closed__0));
if (v___y_859_ == 0)
{
lean_del_object(v___x_870_);
lean_dec_ref(v___y_856_);
v___y_819_ = v___x_872_;
v___y_820_ = v_fileName_864_;
v___y_821_ = v_a_868_;
v___y_822_ = v___x_874_;
v___y_823_ = v___y_861_;
v___y_824_ = v___y_860_;
v___y_825_ = v___x_875_;
v_toCold_826_ = v___y_857_;
v___y_827_ = v___y_816_;
goto v___jp_818_;
}
else
{
uint8_t v___x_876_; 
lean_inc(v_a_868_);
v___x_876_ = l_Lean_MessageData_hasTag(v___y_856_, v_a_868_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_879_; 
lean_dec_ref_known(v___x_874_, 1);
lean_dec_ref(v___x_872_);
lean_dec(v_a_868_);
v___x_877_ = lean_box(0);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_877_);
v___x_879_ = v___x_870_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_del_object(v___x_870_);
v___y_819_ = v___x_872_;
v___y_820_ = v_fileName_864_;
v___y_821_ = v_a_868_;
v___y_822_ = v___x_874_;
v___y_823_ = v___y_861_;
v___y_824_ = v___y_860_;
v___y_825_ = v___x_875_;
v_toCold_826_ = v___y_857_;
v___y_827_ = v___y_816_;
goto v___jp_818_;
}
}
}
}
v___jp_882_:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Syntax_getTailPos_x3f(v___y_886_, v___y_888_);
lean_dec(v___y_886_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_inc(v___y_889_);
v___y_856_ = v___y_883_;
v___y_857_ = v___y_885_;
v___y_858_ = v___y_889_;
v___y_859_ = v___y_884_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_885_;
v___y_863_ = v___y_889_;
goto v___jp_855_;
}
else
{
lean_object* v_val_891_; 
v_val_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_890_, 1);
v___y_856_ = v___y_883_;
v___y_857_ = v___y_885_;
v___y_858_ = v___y_889_;
v___y_859_ = v___y_884_;
v___y_860_ = v___y_888_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_885_;
v___y_863_ = v_val_891_;
goto v___jp_855_;
}
}
v___jp_892_:
{
lean_object* v_toCold_896_; lean_object* v_ref_897_; uint8_t v_suppressElabErrors_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v_ref_902_; lean_object* v___x_903_; 
v_toCold_896_ = lean_ctor_get(v___y_815_, 0);
v_ref_897_ = lean_ctor_get(v___y_815_, 2);
v_suppressElabErrors_898_ = lean_ctor_get_uint8(v___y_815_, sizeof(void*)*3 + 2);
v___x_899_ = lean_box(v_suppressElabErrors_898_);
v___x_900_ = lean_box(v___y_893_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_901_, 0, v___x_899_);
lean_closure_set(v___f_901_, 1, v___x_900_);
v_ref_902_ = l_Lean_replaceRef(v_ref_809_, v_ref_897_);
v___x_903_ = l_Lean_Syntax_getPos_x3f(v_ref_902_, v___y_894_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_883_ = v___f_901_;
v___y_884_ = v_suppressElabErrors_898_;
v___y_885_ = v_toCold_896_;
v___y_886_ = v_ref_902_;
v___y_887_ = v___y_895_;
v___y_888_ = v___y_894_;
v___y_889_ = v___x_904_;
goto v___jp_882_;
}
else
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v___x_903_, 1);
v___y_883_ = v___f_901_;
v___y_884_ = v_suppressElabErrors_898_;
v___y_885_ = v_toCold_896_;
v___y_886_ = v_ref_902_;
v___y_887_ = v___y_895_;
v___y_888_ = v___y_894_;
v___y_889_ = v_val_905_;
goto v___jp_882_;
}
}
v___jp_907_:
{
if (v___y_910_ == 0)
{
v___y_893_ = v___y_908_;
v___y_894_ = v___y_909_;
v___y_895_ = v_severity_811_;
goto v___jp_892_;
}
else
{
v___y_893_ = v___y_908_;
v___y_894_ = v___y_909_;
v___y_895_ = v___x_906_;
goto v___jp_892_;
}
}
v___jp_911_:
{
if (v___y_912_ == 0)
{
uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_913_ = 1;
v___x_914_ = l_Lean_instBEqMessageSeverity_beq(v_severity_811_, v___x_913_);
if (v___x_914_ == 0)
{
v___y_908_ = v___y_912_;
v___y_909_ = v___y_912_;
v___y_910_ = v___x_914_;
goto v___jp_907_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_915_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_815_);
v___x_916_ = l_Lean_warningAsError;
v___x_917_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_915_, v___x_916_);
lean_dec_ref(v___x_915_);
v___y_908_ = v___y_912_;
v___y_909_ = v___y_912_;
v___y_910_ = v___x_917_;
goto v___jp_907_;
}
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_msgData_810_);
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg___boxed(lean_object* v_ref_922_, lean_object* v_msgData_923_, lean_object* v_severity_924_, lean_object* v_isSilent_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
uint8_t v_severity_boxed_931_; uint8_t v_isSilent_boxed_932_; lean_object* v_res_933_; 
v_severity_boxed_931_ = lean_unbox(v_severity_924_);
v_isSilent_boxed_932_ = lean_unbox(v_isSilent_925_);
v_res_933_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_922_, v_msgData_923_, v_severity_boxed_931_, v_isSilent_boxed_932_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v_ref_922_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_936_, v_sz_935_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_937_);
return v___x_946_;
}
else
{
lean_object* v_ref_947_; lean_object* v_a_948_; uint8_t v_severity_949_; uint8_t v_isSilent_950_; lean_object* v_data_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_ref_947_ = lean_ctor_get(v___y_942_, 2);
v_a_948_ = lean_array_uget_borrowed(v_as_934_, v_i_936_);
v_severity_949_ = lean_ctor_get_uint8(v_a_948_, sizeof(void*)*5 + 1);
v_isSilent_950_ = lean_ctor_get_uint8(v_a_948_, sizeof(void*)*5 + 2);
v_data_951_ = lean_ctor_get(v_a_948_, 4);
v___x_952_ = lean_box(0);
lean_inc(v_data_951_);
v___x_953_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_947_, v_data_951_, v_severity_949_, v_isSilent_950_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_953_) == 0)
{
size_t v___x_954_; size_t v___x_955_; 
lean_dec_ref_known(v___x_953_, 1);
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_936_, v___x_954_);
v_i_936_ = v___x_955_;
v_b_937_ = v___x_952_;
goto _start;
}
else
{
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3___boxed(lean_object* v_as_957_, lean_object* v_sz_958_, lean_object* v_i_959_, lean_object* v_b_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
size_t v_sz_boxed_968_; size_t v_i_boxed_969_; lean_object* v_res_970_; 
v_sz_boxed_968_ = lean_unbox_usize(v_sz_958_);
lean_dec(v_sz_958_);
v_i_boxed_969_ = lean_unbox_usize(v_i_959_);
lean_dec(v_i_959_);
v_res_970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v_as_957_, v_sz_boxed_968_, v_i_boxed_969_, v_b_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec_ref(v_as_957_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(uint8_t v_flag_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; lean_object* v_infoState_975_; lean_object* v_env_976_; lean_object* v_nextMacroScope_977_; lean_object* v_ngen_978_; lean_object* v_auxDeclNGen_979_; lean_object* v_traceState_980_; lean_object* v_cache_981_; lean_object* v_recordedDeps_982_; lean_object* v_messages_983_; lean_object* v_snapshotTasks_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1004_; 
v___x_974_ = lean_st_ref_take(v___y_972_);
v_infoState_975_ = lean_ctor_get(v___x_974_, 8);
v_env_976_ = lean_ctor_get(v___x_974_, 0);
v_nextMacroScope_977_ = lean_ctor_get(v___x_974_, 1);
v_ngen_978_ = lean_ctor_get(v___x_974_, 2);
v_auxDeclNGen_979_ = lean_ctor_get(v___x_974_, 3);
v_traceState_980_ = lean_ctor_get(v___x_974_, 4);
v_cache_981_ = lean_ctor_get(v___x_974_, 5);
v_recordedDeps_982_ = lean_ctor_get(v___x_974_, 6);
v_messages_983_ = lean_ctor_get(v___x_974_, 7);
v_snapshotTasks_984_ = lean_ctor_get(v___x_974_, 9);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_986_ = v___x_974_;
v_isShared_987_ = v_isSharedCheck_1004_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_snapshotTasks_984_);
lean_inc(v_infoState_975_);
lean_inc(v_messages_983_);
lean_inc(v_recordedDeps_982_);
lean_inc(v_cache_981_);
lean_inc(v_traceState_980_);
lean_inc(v_auxDeclNGen_979_);
lean_inc(v_ngen_978_);
lean_inc(v_nextMacroScope_977_);
lean_inc(v_env_976_);
lean_dec(v___x_974_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1004_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_assignment_988_; lean_object* v_lazyAssignment_989_; lean_object* v_trees_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1003_; 
v_assignment_988_ = lean_ctor_get(v_infoState_975_, 0);
v_lazyAssignment_989_ = lean_ctor_get(v_infoState_975_, 1);
v_trees_990_ = lean_ctor_get(v_infoState_975_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_infoState_975_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_992_ = v_infoState_975_;
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_trees_990_);
lean_inc(v_lazyAssignment_989_);
lean_inc(v_assignment_988_);
lean_dec(v_infoState_975_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1003_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
if (v_isShared_993_ == 0)
{
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_assignment_988_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_lazyAssignment_989_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_trees_990_);
v___x_996_ = v_reuseFailAlloc_1002_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*3, v_flag_971_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 8, v___x_996_);
v___x_998_ = v___x_986_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_env_976_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_nextMacroScope_977_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_ngen_978_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_auxDeclNGen_979_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_traceState_980_);
lean_ctor_set(v_reuseFailAlloc_1001_, 5, v_cache_981_);
lean_ctor_set(v_reuseFailAlloc_1001_, 6, v_recordedDeps_982_);
lean_ctor_set(v_reuseFailAlloc_1001_, 7, v_messages_983_);
lean_ctor_set(v_reuseFailAlloc_1001_, 8, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1001_, 9, v_snapshotTasks_984_);
v___x_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_st_ref_put(v___y_972_, v___x_998_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_994_);
return v___x_1000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg___boxed(lean_object* v_flag_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
uint8_t v_flag_boxed_1008_; lean_object* v_res_1009_; 
v_flag_boxed_1008_ = lean_unbox(v_flag_1005_);
v_res_1009_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_boxed_1008_, v___y_1006_);
lean_dec(v___y_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(uint8_t v_flag_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v_infoState_1020_; uint8_t v_enabled_1021_; lean_object* v_a_1023_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1019_ = lean_st_ref_get(v___y_1017_);
v_infoState_1020_ = lean_ctor_get(v___x_1019_, 8);
lean_inc_ref(v_infoState_1020_);
lean_dec(v___x_1019_);
v_enabled_1021_ = lean_ctor_get_uint8(v_infoState_1020_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1020_);
v___x_1033_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1010_, v___y_1017_);
lean_dec_ref(v___x_1033_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
v___x_1034_ = lean_apply_7(v_x_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, lean_box(0));
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1021_, v___y_1017_);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1044_);
v___x_1038_ = v___x_1036_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_dec(v___x_1036_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_a_1035_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1035_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
lean_object* v_a_1045_; 
v_a_1045_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1045_);
lean_dec_ref_known(v___x_1034_, 1);
v_a_1023_ = v_a_1045_;
goto v___jp_1022_;
}
v___jp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v___x_1024_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_enabled_1021_, v___y_1017_);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1032_);
v___x_1026_ = v___x_1024_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_dec(v___x_1024_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
lean_ctor_set(v___x_1026_, 0, v_a_1023_);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1023_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg___boxed(lean_object* v_flag_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v_flag_boxed_1055_; lean_object* v_res_1056_; 
v_flag_boxed_1055_ = lean_unbox(v_flag_1046_);
v_res_1056_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_boxed_1055_, v_x_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(lean_object* v_declName_1057_, lean_object* v_binders_1058_, lean_object* v_blocks_1059_, lean_object* v_fileMap_x3f_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1066_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v_a_1071_; size_t v_sz_1089_; size_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___y_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v_sz_1089_ = lean_array_size(v_blocks_1059_);
v___x_1090_ = ((size_t)0ULL);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__0(v_sz_1089_, v___x_1090_, v_blocks_1059_);
v___x_1092_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1092_, 0, v___x_1091_);
v___x_1093_ = 1;
v___x_1094_ = lean_box(v___x_1093_);
v___y_1095_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___lam__0___boxed), 12, 5);
lean_closure_set(v___y_1095_, 0, v_fileMap_x3f_1060_);
lean_closure_set(v___y_1095_, 1, v_declName_1057_);
lean_closure_set(v___y_1095_, 2, v_binders_1058_);
lean_closure_set(v___y_1095_, 3, v___x_1092_);
lean_closure_set(v___y_1095_, 4, v___x_1094_);
v___x_1096_ = 0;
v___x_1097_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v___x_1096_, v___y_1095_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = l_Lean_Core_getAndEmptyMessageLog___redArg(v_a_1066_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = l_Lean_Core_setMessageLog___redArg(v_a_1069_, v_a_1066_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; size_t v_sz_1104_; lean_object* v___x_1105_; 
lean_dec_ref_known(v___x_1101_, 1);
v___x_1102_ = l_Lean_MessageLog_toArray(v_a_1100_);
lean_dec(v_a_1100_);
v___x_1103_ = lean_box(0);
v_sz_1104_ = lean_array_size(v___x_1102_);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__3(v___x_1102_, v_sz_1104_, v___x_1090_, v___x_1103_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec_ref(v___x_1102_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1130_; 
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v___x_1105_, 0);
lean_dec(v_unused_1131_);
v___x_1107_ = v___x_1105_;
v_isShared_1108_ = v_isSharedCheck_1130_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v___x_1105_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1130_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1129_; 
v_fst_1109_ = lean_ctor_get(v_a_1098_, 0);
v_snd_1110_ = lean_ctor_get(v_a_1098_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1112_ = v_a_1098_;
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_snd_1110_);
lean_inc(v_fst_1109_);
lean_dec(v_a_1098_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_fst_1114_; lean_object* v_snd_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1128_; 
v_fst_1114_ = lean_ctor_get(v_fst_1109_, 0);
v_snd_1115_ = lean_ctor_get(v_fst_1109_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_fst_1109_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1117_ = v_fst_1109_;
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_snd_1115_);
lean_inc(v_fst_1114_);
lean_dec(v_fst_1109_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1128_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_fst_1114_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_snd_1115_);
v___x_1120_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1120_);
v___x_1122_ = v___x_1112_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_snd_1110_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1122_);
v___x_1124_ = v___x_1107_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_a_1098_);
v_a_1132_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1105_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1105_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_a_1100_);
lean_dec(v_a_1098_);
v_a_1140_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1101_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1101_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
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
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1148_; 
lean_dec(v_a_1098_);
v_a_1148_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1099_, 1);
v_a_1071_ = v_a_1148_;
goto v___jp_1070_;
}
}
else
{
lean_object* v_a_1149_; 
v_a_1149_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1097_, 1);
v_a_1071_ = v_a_1149_;
goto v___jp_1070_;
}
v___jp_1070_:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Core_setMessageLog___redArg(v_a_1069_, v_a_1066_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v___x_1072_, 0);
lean_dec(v_unused_1080_);
v___x_1074_ = v___x_1072_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___x_1072_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set_tag(v___x_1074_, 1);
lean_ctor_set(v___x_1074_, 0, v_a_1071_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1071_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v_a_1071_);
v_a_1081_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1072_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1072_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_fileMap_x3f_1060_);
lean_dec_ref(v_blocks_1059_);
lean_dec(v_binders_1058_);
lean_dec(v_declName_1057_);
v_a_1150_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1068_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1068_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Add_0__Lean_execVersoBlocks___boxed(lean_object* v_declName_1158_, lean_object* v_binders_1159_, lean_object* v_blocks_1160_, lean_object* v_fileMap_x3f_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1158_, v_binders_1159_, v_blocks_1160_, v_fileMap_x3f_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(uint8_t v_flag_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___redArg(v_flag_1170_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1___boxed(lean_object* v_flag_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_flag_boxed_1187_; lean_object* v_res_1188_; 
v_flag_boxed_1187_ = lean_unbox(v_flag_1179_);
v_res_1188_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1_spec__1(v_flag_boxed_1187_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(lean_object* v_00_u03b1_1189_, uint8_t v_flag_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___redArg(v_flag_1190_, v_x_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_flag_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v_flag_boxed_1210_; lean_object* v_res_1211_; 
v_flag_boxed_1210_ = lean_unbox(v_flag_1201_);
v_res_1211_ = l_Lean_Elab_withEnableInfoTree___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__1(v_00_u03b1_1200_, v_flag_boxed_1210_, v_x_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(lean_object* v_ref_1212_, lean_object* v_msgData_1213_, uint8_t v_severity_1214_, uint8_t v_isSilent_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1212_, v_msgData_1213_, v_severity_1214_, v_isSilent_1215_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___boxed(lean_object* v_ref_1224_, lean_object* v_msgData_1225_, lean_object* v_severity_1226_, lean_object* v_isSilent_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v_severity_boxed_1235_; uint8_t v_isSilent_boxed_1236_; lean_object* v_res_1237_; 
v_severity_boxed_1235_ = lean_unbox(v_severity_1226_);
v_isSilent_boxed_1236_ = lean_unbox(v_isSilent_1227_);
v_res_1237_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2(v_ref_1224_, v_msgData_1225_, v_severity_boxed_1235_, v_isSilent_boxed_1236_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v_ref_1224_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(lean_object* v_msgData_1238_, uint8_t v_severity_1239_, uint8_t v_isSilent_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_ref_1246_; lean_object* v___x_1247_; 
v_ref_1246_ = lean_ctor_get(v___y_1243_, 2);
v___x_1247_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_1246_, v_msgData_1238_, v_severity_1239_, v_isSilent_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_1248_, lean_object* v_severity_1249_, lean_object* v_isSilent_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v_severity_boxed_1256_; uint8_t v_isSilent_boxed_1257_; lean_object* v_res_1258_; 
v_severity_boxed_1256_ = lean_unbox(v_severity_1249_);
v_isSilent_boxed_1257_ = lean_unbox(v_isSilent_1250_);
v_res_1258_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1248_, v_severity_boxed_1256_, v_isSilent_boxed_1257_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(lean_object* v_msgData_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v___x_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = 2;
v___x_1268_ = 0;
v___x_1269_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1259_, v___x_1267_, v___x_1268_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0___boxed(lean_object* v_msgData_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v_msgData_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(lean_object* v_as_1279_, size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1291_, 0, v_b_1282_);
return v___x_1291_;
}
else
{
lean_object* v_a_1292_; lean_object* v_snd_1293_; lean_object* v_snd_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_a_1292_ = lean_array_uget_borrowed(v_as_1279_, v_i_1281_);
v_snd_1293_ = lean_ctor_get(v_a_1292_, 1);
v_snd_1294_ = lean_ctor_get(v_snd_1293_, 1);
v___x_1295_ = lean_box(0);
lean_inc(v_snd_1294_);
v___x_1296_ = l_Lean_Parser_Error_toString(v_snd_1294_);
v___x_1297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
v___x_1298_ = l_Lean_MessageData_ofFormat(v___x_1297_);
v___x_1299_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_1298_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
if (lean_obj_tag(v___x_1299_) == 0)
{
size_t v___x_1300_; size_t v___x_1301_; 
lean_dec_ref_known(v___x_1299_, 1);
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1281_, v___x_1300_);
v_i_1281_ = v___x_1301_;
v_b_1282_ = v___x_1295_;
goto _start;
}
else
{
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1___boxed(lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
size_t v_sz_boxed_1314_; size_t v_i_boxed_1315_; lean_object* v_res_1316_; 
v_sz_boxed_1314_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1315_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v_as_1303_, v_sz_boxed_1314_, v_i_boxed_1315_, v_b_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec_ref(v_as_1303_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText(lean_object* v_declName_1335_, lean_object* v_binders_1336_, lean_object* v_docComment_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; lean_object* v_toCold_1346_; lean_object* v_env_1347_; lean_object* v_fileName_1348_; lean_object* v_currNamespace_1349_; lean_object* v_openDecls_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1345_ = lean_st_ref_get(v_a_1343_);
v_toCold_1346_ = lean_ctor_get(v_a_1342_, 0);
v_env_1347_ = lean_ctor_get(v___x_1345_, 0);
lean_inc_ref_n(v_env_1347_, 2);
lean_dec(v___x_1345_);
v_fileName_1348_ = lean_ctor_get(v_toCold_1346_, 0);
v_currNamespace_1349_ = lean_ctor_get(v_toCold_1346_, 4);
v_openDecls_1350_ = lean_ctor_get(v_toCold_1346_, 5);
v___x_1351_ = lean_string_utf8_byte_size(v_docComment_1337_);
lean_inc_ref_n(v_docComment_1337_, 2);
v___x_1352_ = l_Lean_FileMap_ofString(v_docComment_1337_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v_fileName_1348_);
v___x_1353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1353_, 0, v_docComment_1337_);
lean_ctor_set(v___x_1353_, 1, v_fileName_1348_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_ctor_set(v___x_1353_, 3, v___x_1351_);
v___x_1354_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1342_);
lean_inc(v_openDecls_1350_);
lean_inc(v_currNamespace_1349_);
v___x_1355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1355_, 0, v_env_1347_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
lean_ctor_set(v___x_1355_, 2, v_currNamespace_1349_);
lean_ctor_set(v___x_1355_, 3, v_openDecls_1350_);
v___x_1356_ = l_Lean_Parser_mkParserState(v_docComment_1337_);
lean_dec_ref(v_docComment_1337_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__2));
v___x_1359_ = l_Lean_Parser_getTokenTable(v_env_1347_);
v___x_1360_ = l_Lean_Parser_ParserFn_run(v___x_1358_, v___x_1353_, v___x_1355_, v___x_1359_, v___x_1356_);
lean_inc_ref(v___x_1360_);
v___x_1361_ = l_Lean_Parser_ParserState_allErrors(v___x_1360_);
v___x_1362_ = lean_array_get_size(v___x_1361_);
v___x_1363_ = lean_nat_dec_eq(v___x_1362_, v___x_1357_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; size_t v_sz_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1352_);
lean_dec(v_binders_1336_);
lean_dec(v_declName_1335_);
v___x_1364_ = lean_box(0);
v_sz_1365_ = lean_array_size(v___x_1361_);
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_versoDocStringOfText_spec__1(v___x_1361_, v_sz_1365_, v___x_1366_, v___x_1364_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
lean_dec_ref(v___x_1361_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1376_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_a_1377_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1367_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1367_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v_stxStack_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v___x_1361_);
v_stxStack_1385_ = lean_ctor_get(v___x_1360_, 0);
lean_inc_ref(v_stxStack_1385_);
lean_dec_ref(v___x_1360_);
v___x_1386_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1385_);
lean_dec_ref(v_stxStack_1385_);
v___x_1387_ = l_Lean_TSyntax_getVersoBlocks(v___x_1386_);
lean_dec(v___x_1386_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1352_);
v___x_1389_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1335_, v_binders_1336_, v___x_1387_, v___x_1388_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringOfText___boxed(lean_object* v_declName_1390_, lean_object* v_binders_1391_, lean_object* v_docComment_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_versoDocStringOfText(v_declName_1390_, v_binders_1391_, v_docComment_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
lean_dec(v_a_1398_);
lean_dec_ref(v_a_1397_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(lean_object* v_msgData_1401_, uint8_t v_severity_1402_, uint8_t v_isSilent_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___redArg(v_msgData_1401_, v_severity_1402_, v_isSilent_1403_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0___boxed(lean_object* v_msgData_1412_, lean_object* v_severity_1413_, lean_object* v_isSilent_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
uint8_t v_severity_boxed_1422_; uint8_t v_isSilent_boxed_1423_; lean_object* v_res_1424_; 
v_severity_boxed_1422_ = lean_unbox(v_severity_1413_);
v_isSilent_boxed_1423_ = lean_unbox(v_isSilent_1414_);
v_res_1424_ = l_Lean_log___at___00Lean_logError___at___00Lean_versoDocStringOfText_spec__0_spec__0(v_msgData_1412_, v_severity_boxed_1422_, v_isSilent_boxed_1423_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString(lean_object* v_declName_1434_, lean_object* v_binders_1435_, lean_object* v_docComment_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Lean_DocString_Add_0__Lean_docStringRange(v_docComment_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1445_; lean_object* v_body_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
lean_dec_ref_known(v___x_1444_, 1);
v___x_1445_ = lean_unsigned_to_nat(1u);
v_body_1446_ = l_Lean_Syntax_getArg(v_docComment_1436_, v___x_1445_);
v___x_1447_ = ((lean_object*)(l_Lean_versoDocString___closed__4));
v___x_1448_ = l_Lean_Syntax_isOfKind(v_body_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = l_Lean_TSyntax_getDocString(v_docComment_1436_);
v___x_1450_ = l_Lean_versoDocStringOfText(v_declName_1434_, v_binders_1435_, v___x_1449_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v_markup_1452_; 
v___x_1451_ = l_Lean_VersoDocstringView_of(v_docComment_1436_);
v_markup_1452_ = lean_ctor_get(v___x_1451_, 1);
lean_inc_ref(v_markup_1452_);
lean_dec_ref(v___x_1451_);
if (lean_obj_tag(v_markup_1452_) == 0)
{
lean_object* v_doc_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_doc_1453_ = lean_ctor_get(v_markup_1452_, 0);
lean_inc(v_doc_1453_);
lean_dec_ref_known(v_markup_1452_, 1);
v___x_1454_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1453_);
lean_dec(v_doc_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = l___private_Lean_DocString_Add_0__Lean_execVersoBlocks(v_declName_1434_, v_binders_1435_, v___x_1454_, v___x_1455_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1456_;
}
else
{
lean_object* v_text_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_text_1457_ = lean_ctor_get(v_markup_1452_, 0);
lean_inc(v_text_1457_);
lean_dec_ref_known(v_markup_1452_, 1);
v___x_1458_ = l_Lean_Syntax_getAtomVal(v_text_1457_);
lean_dec(v_text_1457_);
v___x_1459_ = l_Lean_versoDocStringOfText(v_declName_1434_, v_binders_1435_, v___x_1458_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
return v___x_1459_;
}
}
}
else
{
lean_object* v___x_1460_; 
lean_dec_ref_known(v___x_1444_, 1);
v___x_1460_ = l_Lean_parseVersoDocString(v_docComment_1436_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1508_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1508_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1508_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (lean_obj_tag(v_a_1461_) == 1)
{
lean_object* v_val_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1463_);
v_val_1465_ = lean_ctor_get(v_a_1461_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_a_1461_, 1);
v___x_1466_ = l_Lean_TSyntax_getVersoBlocks(v_val_1465_);
lean_dec(v_val_1465_);
v___x_1467_ = lean_alloc_closure((void*)(l_Lean_Doc_elabBlocks___boxed), 11, 1);
lean_closure_set(v___x_1467_, 0, v___x_1466_);
v___x_1468_ = 0;
v___x_1469_ = l_Lean_Doc_DocM_exec___redArg(v_declName_1434_, v_binders_1435_, v___x_1467_, v___x_1468_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1495_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1495_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1495_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v_fst_1474_; lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1494_; 
v_fst_1474_ = lean_ctor_get(v_a_1470_, 0);
v_snd_1475_ = lean_ctor_get(v_a_1470_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1477_ = v_a_1470_;
v_isShared_1478_ = v_isSharedCheck_1494_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_inc(v_fst_1474_);
lean_dec(v_a_1470_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1494_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1493_; 
v_fst_1479_ = lean_ctor_get(v_fst_1474_, 0);
v_snd_1480_ = lean_ctor_get(v_fst_1474_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_fst_1474_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1482_ = v_fst_1474_;
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snd_1480_);
lean_inc(v_fst_1479_);
lean_dec(v_fst_1474_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1493_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_fst_1479_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_snd_1480_);
v___x_1485_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1487_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1485_);
v___x_1487_ = v___x_1477_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_snd_1475_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1487_);
v___x_1489_ = v___x_1472_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1469_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1469_);
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
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_a_1461_);
lean_dec(v_binders_1435_);
lean_dec(v_declName_1434_);
v___x_1504_ = ((lean_object*)(l_Lean_versoDocStringOfText___closed__5));
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1504_);
v___x_1506_ = v___x_1463_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_binders_1435_);
lean_dec(v_declName_1434_);
v_a_1509_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1460_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1460_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocString___boxed(lean_object* v_declName_1517_, lean_object* v_binders_1518_, lean_object* v_docComment_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_versoDocString(v_declName_1517_, v_binders_1518_, v_docComment_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_docComment_1519_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString(lean_object* v_range_1528_, lean_object* v_doc_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v_val_1545_; lean_object* v_env_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1537_ = lean_st_ref_get(v_a_1535_);
v_env_1547_ = lean_ctor_get(v___x_1537_, 0);
lean_inc_ref(v_env_1547_);
lean_dec(v___x_1537_);
v___x_1548_ = l_Lean_getMainVersoModuleDocs(v_env_1547_);
v___x_1549_ = l_Lean_VersoModuleDocs_terminalNesting(v___x_1548_);
lean_dec_ref(v___x_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1529_);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___y_1539_ = v___x_1550_;
v___y_1540_ = v___x_1551_;
goto v___jp_1538_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1549_, 1);
v_val_1545_ = v_val_1552_;
goto v___jp_1544_;
}
}
else
{
lean_object* v_val_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_val_1553_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_val_1553_, v___x_1554_);
lean_dec(v_val_1553_);
v_val_1545_ = v___x_1555_;
goto v___jp_1544_;
}
v___jp_1538_:
{
lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_alloc_closure((void*)(l_Lean_Doc_elabModSnippet___boxed), 13, 3);
lean_closure_set(v___x_1541_, 0, v_range_1528_);
lean_closure_set(v___x_1541_, 1, v___y_1539_);
lean_closure_set(v___x_1541_, 2, v___y_1540_);
v___x_1542_ = 0;
v___x_1543_ = l_Lean_Doc_DocM_execForModule___redArg(v___x_1541_, v___x_1542_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1543_;
}
v___jp_1544_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_TSyntax_getVersoBlocks(v_doc_1529_);
v___y_1539_ = v___x_1546_;
v___y_1540_ = v_val_1545_;
goto v___jp_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_versoModDocString___boxed(lean_object* v_range_1556_, lean_object* v_doc_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_versoModDocString(v_range_1556_, v_doc_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec_ref(v_a_1560_);
lean_dec(v_a_1559_);
lean_dec_ref(v_a_1558_);
lean_dec(v_doc_1557_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString(lean_object* v_declName_1575_, lean_object* v_docComment_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = ((lean_object*)(l_Lean_versoDocStringFromString___closed__3));
v___x_1585_ = l_Lean_versoDocStringOfText(v_declName_1575_, v___x_1584_, v_docComment_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_versoDocStringFromString___boxed(lean_object* v_declName_1586_, lean_object* v_docComment_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_versoDocStringFromString(v_declName_1586_, v_docComment_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1593_);
lean_dec_ref(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec_ref(v_a_1590_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0(lean_object* v_docString_1596_, lean_object* v_declName_1597_, uint8_t v___x_1598_, lean_object* v_env_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = l_Lean_docStringExt;
v___x_1601_ = l_String_removeLeadingSpaces(v_docString_1596_);
v___x_1602_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1600_, v_env_1599_, v_declName_1597_, v___x_1601_, v___x_1598_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__0___boxed(lean_object* v_docString_1603_, lean_object* v_declName_1604_, lean_object* v___x_1605_, lean_object* v_env_1606_){
_start:
{
uint8_t v___x_183__boxed_1607_; lean_object* v_res_1608_; 
v___x_183__boxed_1607_ = lean_unbox(v___x_1605_);
v_res_1608_ = l_Lean_addMarkdownDocString___redArg___lam__0(v_docString_1603_, v_declName_1604_, v___x_183__boxed_1607_, v_env_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1(lean_object* v_declName_1609_, uint8_t v___x_1610_, lean_object* v_modifyEnv_1611_, lean_object* v_docString_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___f_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_box(v___x_1610_);
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1614_, 0, v_docString_1612_);
lean_closure_set(v___f_1614_, 1, v_declName_1609_);
lean_closure_set(v___f_1614_, 2, v___x_1613_);
v___x_1615_ = lean_apply_1(v_modifyEnv_1611_, v___f_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__1___boxed(lean_object* v_declName_1616_, lean_object* v___x_1617_, lean_object* v_modifyEnv_1618_, lean_object* v_docString_1619_){
_start:
{
uint8_t v___x_192__boxed_1620_; lean_object* v_res_1621_; 
v___x_192__boxed_1620_ = lean_unbox(v___x_1617_);
v_res_1621_ = l_Lean_addMarkdownDocString___redArg___lam__1(v_declName_1616_, v___x_192__boxed_1620_, v_modifyEnv_1618_, v_docString_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__2(lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_docComment_1624_, lean_object* v_toBind_1625_, lean_object* v___f_1626_, lean_object* v_____r_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = l_Lean_getDocStringText___redArg(v_inst_1622_, v_inst_1623_, v_docComment_1624_);
v___x_1629_ = lean_apply_4(v_toBind_1625_, lean_box(0), lean_box(0), v___x_1628_, v___f_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3(lean_object* v_inst_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_inst_1634_, lean_object* v_docComment_1635_, lean_object* v_toBind_1636_, lean_object* v___f_1637_, lean_object* v_____r_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l_Lean_validateDocComment___redArg(v_inst_1630_, v_inst_1631_, v_inst_1632_, v_inst_1633_, v_inst_1634_, v_docComment_1635_);
v___x_1640_ = lean_apply_4(v_toBind_1636_, lean_box(0), lean_box(0), v___x_1639_, v___f_1637_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__3___boxed(lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_docComment_1646_, lean_object* v_toBind_1647_, lean_object* v___f_1648_, lean_object* v_____r_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_addMarkdownDocString___redArg___lam__3(v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_docComment_1646_, v_toBind_1647_, v___f_1648_, v_____r_1649_);
lean_dec(v_docComment_1646_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__4(lean_object* v___f_1651_, lean_object* v_____r_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_apply_1(v___f_1651_, v_____r_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__0));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l_Lean_addMarkdownDocString___redArg___lam__5___closed__2));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5(lean_object* v___f_1660_, lean_object* v_declName_1661_, uint8_t v___x_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_toBind_1665_, lean_object* v___f_1666_, lean_object* v_____do__lift_1667_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1667_, v_declName_1661_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_dec(v___f_1666_);
lean_dec(v_toBind_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec_ref(v_inst_1663_);
lean_dec(v_declName_1661_);
goto v___jp_1668_;
}
else
{
lean_dec_ref_known(v___x_1671_, 1);
if (v___x_1662_ == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___f_1660_);
v___x_1672_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_1673_ = l_Lean_MessageData_ofConstName(v_declName_1661_, v___x_1662_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_throwError___redArg(v_inst_1663_, v_inst_1664_, v___x_1676_);
v___x_1678_ = lean_apply_4(v_toBind_1665_, lean_box(0), lean_box(0), v___x_1677_, v___f_1666_);
return v___x_1678_;
}
else
{
lean_dec(v___f_1666_);
lean_dec(v_toBind_1665_);
lean_dec_ref(v_inst_1664_);
lean_dec_ref(v_inst_1663_);
lean_dec(v_declName_1661_);
goto v___jp_1668_;
}
}
v___jp_1668_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_apply_1(v___f_1660_, v___x_1669_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg___lam__5___boxed(lean_object* v___f_1679_, lean_object* v_declName_1680_, lean_object* v___x_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_toBind_1684_, lean_object* v___f_1685_, lean_object* v_____do__lift_1686_){
_start:
{
uint8_t v___x_257__boxed_1687_; lean_object* v_res_1688_; 
v___x_257__boxed_1687_ = lean_unbox(v___x_1681_);
v_res_1688_ = l_Lean_addMarkdownDocString___redArg___lam__5(v___f_1679_, v_declName_1680_, v___x_257__boxed_1687_, v_inst_1682_, v_inst_1683_, v_toBind_1684_, v___f_1685_, v_____do__lift_1686_);
lean_dec_ref(v_____do__lift_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___redArg(lean_object* v_inst_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_declName_1696_, lean_object* v_docComment_1697_){
_start:
{
lean_object* v_toApplicative_1698_; lean_object* v_toBind_1699_; lean_object* v_toPure_1700_; uint8_t v___x_1701_; 
v_toApplicative_1698_ = lean_ctor_get(v_inst_1689_, 0);
v_toBind_1699_ = lean_ctor_get(v_inst_1689_, 1);
lean_inc(v_toBind_1699_);
v_toPure_1700_ = lean_ctor_get(v_toApplicative_1698_, 1);
v___x_1701_ = l_Lean_Name_isAnonymous(v_declName_1696_);
if (v___x_1701_ == 0)
{
lean_object* v_getEnv_1702_; lean_object* v_modifyEnv_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___x_1712_; 
v_getEnv_1702_ = lean_ctor_get(v_inst_1692_, 0);
lean_inc(v_getEnv_1702_);
v_modifyEnv_1703_ = lean_ctor_get(v_inst_1692_, 1);
lean_inc(v_modifyEnv_1703_);
lean_dec_ref(v_inst_1692_);
v___x_1704_ = 1;
v___x_1705_ = lean_box(v___x_1704_);
lean_inc(v_declName_1696_);
v___f_1706_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1706_, 0, v_declName_1696_);
lean_closure_set(v___f_1706_, 1, v___x_1705_);
lean_closure_set(v___f_1706_, 2, v_modifyEnv_1703_);
lean_inc_n(v_toBind_1699_, 3);
lean_inc(v_docComment_1697_);
lean_inc_ref(v_inst_1693_);
lean_inc_ref_n(v_inst_1689_, 2);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1707_, 0, v_inst_1689_);
lean_closure_set(v___f_1707_, 1, v_inst_1693_);
lean_closure_set(v___f_1707_, 2, v_docComment_1697_);
lean_closure_set(v___f_1707_, 3, v_toBind_1699_);
lean_closure_set(v___f_1707_, 4, v___f_1706_);
v___f_1708_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(v___f_1708_, 0, v_inst_1689_);
lean_closure_set(v___f_1708_, 1, v_inst_1690_);
lean_closure_set(v___f_1708_, 2, v_inst_1694_);
lean_closure_set(v___f_1708_, 3, v_inst_1695_);
lean_closure_set(v___f_1708_, 4, v_inst_1691_);
lean_closure_set(v___f_1708_, 5, v_docComment_1697_);
lean_closure_set(v___f_1708_, 6, v_toBind_1699_);
lean_closure_set(v___f_1708_, 7, v___f_1707_);
lean_inc_ref(v___f_1708_);
v___f_1709_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__4), 2, 1);
lean_closure_set(v___f_1709_, 0, v___f_1708_);
v___x_1710_ = lean_box(v___x_1701_);
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_addMarkdownDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_1711_, 0, v___f_1708_);
lean_closure_set(v___f_1711_, 1, v_declName_1696_);
lean_closure_set(v___f_1711_, 2, v___x_1710_);
lean_closure_set(v___f_1711_, 3, v_inst_1689_);
lean_closure_set(v___f_1711_, 4, v_inst_1693_);
lean_closure_set(v___f_1711_, 5, v_toBind_1699_);
lean_closure_set(v___f_1711_, 6, v___f_1709_);
v___x_1712_ = lean_apply_4(v_toBind_1699_, lean_box(0), lean_box(0), v_getEnv_1702_, v___f_1711_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_inc(v_toPure_1700_);
lean_dec(v_toBind_1699_);
lean_dec(v_docComment_1697_);
lean_dec(v_declName_1696_);
lean_dec(v_inst_1695_);
lean_dec_ref(v_inst_1694_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
lean_dec_ref(v_inst_1691_);
lean_dec(v_inst_1690_);
lean_dec_ref(v_inst_1689_);
v___x_1713_ = lean_box(0);
v___x_1714_ = lean_apply_2(v_toPure_1700_, lean_box(0), v___x_1713_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString(lean_object* v_m_1715_, lean_object* v_inst_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_declName_1723_, lean_object* v_docComment_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_addMarkdownDocString___redArg(v_inst_1716_, v_inst_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_declName_1723_, v_docComment_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__0(lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_s_1728_){
_start:
{
lean_object* v_addEntryFn_1729_; lean_object* v_importedEntries_1730_; lean_object* v_state_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_addEntryFn_1729_ = lean_ctor_get(v___x_1726_, 3);
lean_inc(v_addEntryFn_1729_);
lean_dec_ref(v___x_1726_);
v_importedEntries_1730_ = lean_ctor_get(v_s_1728_, 0);
v_state_1731_ = lean_ctor_get(v_s_1728_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_s_1728_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v_s_1728_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_state_1731_);
lean_inc(v_importedEntries_1730_);
lean_dec(v_s_1728_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_state_1735_; lean_object* v___x_1737_; 
v_state_1735_ = lean_apply_2(v_addEntryFn_1729_, v_state_1731_, v___x_1727_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_state_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_importedEntries_1730_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_state_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__1(lean_object* v_declName_1740_, lean_object* v_x1_1741_, lean_object* v_x2_1742_){
_start:
{
lean_object* v_index_1743_; lean_object* v_sourceString_1744_; lean_object* v_imports_1745_; lean_object* v_currNamespace_1746_; lean_object* v_openDecls_1747_; lean_object* v_options_1748_; lean_object* v_check_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1767_; 
v_index_1743_ = lean_ctor_get(v_x2_1742_, 1);
v_sourceString_1744_ = lean_ctor_get(v_x2_1742_, 2);
v_imports_1745_ = lean_ctor_get(v_x2_1742_, 3);
v_currNamespace_1746_ = lean_ctor_get(v_x2_1742_, 4);
v_openDecls_1747_ = lean_ctor_get(v_x2_1742_, 5);
v_options_1748_ = lean_ctor_get(v_x2_1742_, 6);
v_check_1749_ = lean_ctor_get(v_x2_1742_, 7);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_x2_1742_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v_x2_1742_, 0);
lean_dec(v_unused_1768_);
v___x_1751_ = v_x2_1742_;
v_isShared_1752_ = v_isSharedCheck_1767_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_check_1749_);
lean_inc(v_options_1748_);
lean_inc(v_openDecls_1747_);
lean_inc(v_currNamespace_1746_);
lean_inc(v_imports_1745_);
lean_inc(v_sourceString_1744_);
lean_inc(v_index_1743_);
lean_dec(v_x2_1742_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1767_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v_toEnvExtension_1754_; lean_object* v_asyncMode_1755_; uint8_t v_logWrites_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1753_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1754_ = lean_ctor_get(v___x_1753_, 0);
v_asyncMode_1755_ = lean_ctor_get(v_toEnvExtension_1754_, 2);
v_logWrites_1756_ = lean_ctor_get_uint8(v_toEnvExtension_1754_, sizeof(void*)*6);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_declName_1740_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1757_);
v___x_1759_ = v___x_1751_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_index_1743_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_sourceString_1744_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_imports_1745_);
lean_ctor_set(v_reuseFailAlloc_1766_, 4, v_currNamespace_1746_);
lean_ctor_set(v_reuseFailAlloc_1766_, 5, v_openDecls_1747_);
lean_ctor_set(v_reuseFailAlloc_1766_, 6, v_options_1748_);
lean_ctor_set(v_reuseFailAlloc_1766_, 7, v_check_1749_);
v___x_1759_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___f_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1760_, 0, v___x_1753_);
lean_closure_set(v___f_1760_, 1, v___x_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = 1;
if (v_logWrites_1756_ == 0)
{
lean_object* v___x_1763_; 
lean_inc_ref(v_toEnvExtension_1754_);
v___x_1763_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1754_, v_x1_1741_, v___f_1760_, v_asyncMode_1755_, v___x_1761_, v___x_1762_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_inc_ref_n(v_toEnvExtension_1754_, 2);
v___x_1764_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1754_, v_x1_1741_);
lean_dec_ref(v_x1_1741_);
v___x_1765_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1754_, v___x_1764_, v___f_1760_, v_asyncMode_1755_, v___x_1761_, v___x_1762_);
return v___x_1765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2(lean_object* v_declName_1788_, lean_object* v_docs_1789_, uint8_t v___x_1790_, lean_object* v_deferred_1791_, lean_object* v___f_1792_, lean_object* v_env_1793_){
_start:
{
lean_object* v___x_1794_; lean_object* v_env_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1794_ = l_Lean_versoDocStringExt;
v_env_1795_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1794_, v_env_1793_, v_declName_1788_, v_docs_1789_, v___x_1790_);
v___x_1796_ = lean_unsigned_to_nat(0u);
v___x_1797_ = lean_array_get_size(v_deferred_1791_);
v___x_1798_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1799_ = lean_nat_dec_lt(v___x_1796_, v___x_1797_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v___f_1792_);
lean_dec_ref(v_deferred_1791_);
return v_env_1795_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v___x_1797_, v___x_1797_);
if (v___x_1800_ == 0)
{
if (v___x_1799_ == 0)
{
lean_dec_ref(v___f_1792_);
lean_dec_ref(v_deferred_1791_);
return v_env_1795_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1797_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1798_, v___f_1792_, v_deferred_1791_, v___x_1801_, v___x_1802_, v_env_1795_);
return v___x_1803_;
}
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1797_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1798_, v___f_1792_, v_deferred_1791_, v___x_1804_, v___x_1805_, v_env_1795_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__2___boxed(lean_object* v_declName_1807_, lean_object* v_docs_1808_, lean_object* v___x_1809_, lean_object* v_deferred_1810_, lean_object* v___f_1811_, lean_object* v_env_1812_){
_start:
{
uint8_t v___x_379__boxed_1813_; lean_object* v_res_1814_; 
v___x_379__boxed_1813_ = lean_unbox(v___x_1809_);
v_res_1814_ = l_Lean_addVersoDocStringCore___redArg___lam__2(v_declName_1807_, v_docs_1808_, v___x_379__boxed_1813_, v_deferred_1810_, v___f_1811_, v_env_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__3(lean_object* v_modifyEnv_1815_, lean_object* v___f_1816_, lean_object* v_____r_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_apply_1(v_modifyEnv_1815_, v___f_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4(lean_object* v_declName_1821_, lean_object* v_modifyEnv_1822_, lean_object* v___f_1823_, uint8_t v___x_1824_, uint8_t v___x_1825_, lean_object* v_inst_1826_, lean_object* v_inst_1827_, lean_object* v_toBind_1828_, lean_object* v___f_1829_, lean_object* v_____do__lift_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Environment_getModuleIdxFor_x3f(v_____do__lift_1830_, v_declName_1821_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v___x_1832_; 
lean_dec(v___f_1829_);
lean_dec(v_toBind_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec(v_declName_1821_);
v___x_1832_ = lean_apply_1(v_modifyEnv_1822_, v___f_1823_);
return v___x_1832_;
}
else
{
lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1848_; 
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1831_, 0);
lean_dec(v_unused_1849_);
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
if (v___x_1824_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec_ref(v___f_1823_);
lean_dec(v_modifyEnv_1822_);
v___x_1836_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_1837_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1821_, v___x_1825_);
v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_1840_ = lean_string_append(v___x_1838_, v___x_1839_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 3);
lean_ctor_set(v___x_1834_, 0, v___x_1840_);
v___x_1842_ = v___x_1834_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = l_Lean_MessageData_ofFormat(v___x_1842_);
v___x_1844_ = l_Lean_throwError___redArg(v_inst_1826_, v_inst_1827_, v___x_1843_);
v___x_1845_ = lean_apply_4(v_toBind_1828_, lean_box(0), lean_box(0), v___x_1844_, v___f_1829_);
return v___x_1845_;
}
}
else
{
lean_object* v___x_1847_; 
lean_del_object(v___x_1834_);
lean_dec(v___f_1829_);
lean_dec(v_toBind_1828_);
lean_dec_ref(v_inst_1827_);
lean_dec_ref(v_inst_1826_);
lean_dec(v_declName_1821_);
v___x_1847_ = lean_apply_1(v_modifyEnv_1822_, v___f_1823_);
return v___x_1847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg___lam__4___boxed(lean_object* v_declName_1850_, lean_object* v_modifyEnv_1851_, lean_object* v___f_1852_, lean_object* v___x_1853_, lean_object* v___x_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_toBind_1857_, lean_object* v___f_1858_, lean_object* v_____do__lift_1859_){
_start:
{
uint8_t v___x_439__boxed_1860_; uint8_t v___x_440__boxed_1861_; lean_object* v_res_1862_; 
v___x_439__boxed_1860_ = lean_unbox(v___x_1853_);
v___x_440__boxed_1861_ = lean_unbox(v___x_1854_);
v_res_1862_ = l_Lean_addVersoDocStringCore___redArg___lam__4(v_declName_1850_, v_modifyEnv_1851_, v___f_1852_, v___x_439__boxed_1860_, v___x_440__boxed_1861_, v_inst_1855_, v_inst_1856_, v_toBind_1857_, v___f_1858_, v_____do__lift_1859_);
lean_dec_ref(v_____do__lift_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___redArg(lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_declName_1866_, lean_object* v_docs_1867_, lean_object* v_deferred_1868_){
_start:
{
lean_object* v_toApplicative_1869_; lean_object* v_toBind_1870_; lean_object* v_toPure_1871_; uint8_t v___x_1872_; 
v_toApplicative_1869_ = lean_ctor_get(v_inst_1863_, 0);
v_toBind_1870_ = lean_ctor_get(v_inst_1863_, 1);
lean_inc(v_toBind_1870_);
v_toPure_1871_ = lean_ctor_get(v_toApplicative_1869_, 1);
v___x_1872_ = l_Lean_Name_isAnonymous(v_declName_1866_);
if (v___x_1872_ == 0)
{
lean_object* v_getEnv_1873_; lean_object* v_modifyEnv_1874_; lean_object* v___f_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___f_1878_; lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___x_1883_; 
v_getEnv_1873_ = lean_ctor_get(v_inst_1864_, 0);
lean_inc(v_getEnv_1873_);
v_modifyEnv_1874_ = lean_ctor_get(v_inst_1864_, 1);
lean_inc_n(v_modifyEnv_1874_, 2);
lean_dec_ref(v_inst_1864_);
lean_inc_n(v_declName_1866_, 2);
v___f_1875_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1875_, 0, v_declName_1866_);
v___x_1876_ = 1;
v___x_1877_ = lean_box(v___x_1876_);
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__2___boxed), 6, 5);
lean_closure_set(v___f_1878_, 0, v_declName_1866_);
lean_closure_set(v___f_1878_, 1, v_docs_1867_);
lean_closure_set(v___f_1878_, 2, v___x_1877_);
lean_closure_set(v___f_1878_, 3, v_deferred_1868_);
lean_closure_set(v___f_1878_, 4, v___f_1875_);
lean_inc_ref(v___f_1878_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__3), 3, 2);
lean_closure_set(v___f_1879_, 0, v_modifyEnv_1874_);
lean_closure_set(v___f_1879_, 1, v___f_1878_);
v___x_1880_ = lean_box(v___x_1872_);
v___x_1881_ = lean_box(v___x_1876_);
lean_inc(v_toBind_1870_);
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1882_, 0, v_declName_1866_);
lean_closure_set(v___f_1882_, 1, v_modifyEnv_1874_);
lean_closure_set(v___f_1882_, 2, v___f_1878_);
lean_closure_set(v___f_1882_, 3, v___x_1880_);
lean_closure_set(v___f_1882_, 4, v___x_1881_);
lean_closure_set(v___f_1882_, 5, v_inst_1863_);
lean_closure_set(v___f_1882_, 6, v_inst_1865_);
lean_closure_set(v___f_1882_, 7, v_toBind_1870_);
lean_closure_set(v___f_1882_, 8, v___f_1879_);
v___x_1883_ = lean_apply_4(v_toBind_1870_, lean_box(0), lean_box(0), v_getEnv_1873_, v___f_1882_);
return v___x_1883_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_inc(v_toPure_1871_);
lean_dec(v_toBind_1870_);
lean_dec_ref(v_deferred_1868_);
lean_dec_ref(v_docs_1867_);
lean_dec(v_declName_1866_);
lean_dec_ref(v_inst_1865_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v_inst_1863_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_apply_2(v_toPure_1871_, lean_box(0), v___x_1884_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore(lean_object* v_m_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_declName_1891_, lean_object* v_docs_1892_, lean_object* v_deferred_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_addVersoDocStringCore___redArg(v_inst_1887_, v_inst_1888_, v_inst_1890_, v_declName_1891_, v_docs_1892_, v_deferred_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___boxed(lean_object* v_m_1895_, lean_object* v_inst_1896_, lean_object* v_inst_1897_, lean_object* v_inst_1898_, lean_object* v_inst_1899_, lean_object* v_declName_1900_, lean_object* v_docs_1901_, lean_object* v_deferred_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_addVersoDocStringCore(v_m_1895_, v_inst_1896_, v_inst_1897_, v_inst_1898_, v_inst_1899_, v_declName_1900_, v_docs_1901_, v_deferred_1902_);
lean_dec(v_inst_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1(lean_object* v_size_1904_, uint8_t v___x_1905_, lean_object* v_x1_1906_, lean_object* v_x2_1907_){
_start:
{
lean_object* v_index_1908_; lean_object* v_sourceString_1909_; lean_object* v_imports_1910_; lean_object* v_currNamespace_1911_; lean_object* v_openDecls_1912_; lean_object* v_options_1913_; lean_object* v_check_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1931_; 
v_index_1908_ = lean_ctor_get(v_x2_1907_, 1);
v_sourceString_1909_ = lean_ctor_get(v_x2_1907_, 2);
v_imports_1910_ = lean_ctor_get(v_x2_1907_, 3);
v_currNamespace_1911_ = lean_ctor_get(v_x2_1907_, 4);
v_openDecls_1912_ = lean_ctor_get(v_x2_1907_, 5);
v_options_1913_ = lean_ctor_get(v_x2_1907_, 6);
v_check_1914_ = lean_ctor_get(v_x2_1907_, 7);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_x2_1907_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_x2_1907_, 0);
lean_dec(v_unused_1932_);
v___x_1916_ = v_x2_1907_;
v_isShared_1917_ = v_isSharedCheck_1931_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_check_1914_);
lean_inc(v_options_1913_);
lean_inc(v_openDecls_1912_);
lean_inc(v_currNamespace_1911_);
lean_inc(v_imports_1910_);
lean_inc(v_sourceString_1909_);
lean_inc(v_index_1908_);
lean_dec(v_x2_1907_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1931_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v_toEnvExtension_1919_; lean_object* v_asyncMode_1920_; uint8_t v_logWrites_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1918_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_1919_ = lean_ctor_get(v___x_1918_, 0);
v_asyncMode_1920_ = lean_ctor_get(v_toEnvExtension_1919_, 2);
v_logWrites_1921_ = lean_ctor_get_uint8(v_toEnvExtension_1919_, sizeof(void*)*6);
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_size_1904_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1922_);
v___x_1924_ = v___x_1916_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_index_1908_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_sourceString_1909_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_imports_1910_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_currNamespace_1911_);
lean_ctor_set(v_reuseFailAlloc_1930_, 5, v_openDecls_1912_);
lean_ctor_set(v_reuseFailAlloc_1930_, 6, v_options_1913_);
lean_ctor_set(v_reuseFailAlloc_1930_, 7, v_check_1914_);
v___x_1924_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___f_1925_; lean_object* v___x_1926_; 
v___f_1925_ = lean_alloc_closure((void*)(l_Lean_addVersoDocStringCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1925_, 0, v___x_1918_);
lean_closure_set(v___f_1925_, 1, v___x_1924_);
v___x_1926_ = lean_box(0);
if (v_logWrites_1921_ == 0)
{
lean_object* v___x_1927_; 
lean_inc_ref(v_toEnvExtension_1919_);
v___x_1927_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1919_, v_x1_1906_, v___f_1925_, v_asyncMode_1920_, v___x_1926_, v___x_1905_);
return v___x_1927_;
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_inc_ref_n(v_toEnvExtension_1919_, 2);
v___x_1928_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1919_, v_x1_1906_);
lean_dec_ref(v_x1_1906_);
v___x_1929_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1919_, v___x_1928_, v___f_1925_, v_asyncMode_1920_, v___x_1926_, v___x_1905_);
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed(lean_object* v_size_1933_, lean_object* v___x_1934_, lean_object* v_x1_1935_, lean_object* v_x2_1936_){
_start:
{
uint8_t v___x_313__boxed_1937_; lean_object* v_res_1938_; 
v___x_313__boxed_1937_ = lean_unbox(v___x_1934_);
v_res_1938_ = l_Lean_addVersoModDocStringCore___redArg___lam__1(v_size_1933_, v___x_313__boxed_1937_, v_x1_1935_, v_x2_1936_);
return v_res_1938_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__0));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__0(lean_object* v_docs_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_deferred_1945_, lean_object* v_inst_1946_, lean_object* v___f_1947_, lean_object* v_____do__lift_1948_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_addVersoModuleDocSnippet(v_____do__lift_1948_, v_docs_1942_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v___f_1947_);
lean_dec_ref(v_inst_1946_);
lean_dec_ref(v_deferred_1945_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_1952_ = l_Lean_stringToMessageData(v_a_1950_);
v___x_1953_ = l_Lean_indentD(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1951_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l_Lean_throwError___redArg(v_inst_1943_, v_inst_1944_, v___x_1954_);
return v___x_1955_;
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
lean_dec_ref(v_inst_1944_);
lean_dec_ref(v_inst_1943_);
v_a_1956_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_deferred_1945_);
v___x_1959_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__2___closed__9));
v___x_1960_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v___f_1947_);
lean_dec_ref(v_deferred_1945_);
v___x_1961_ = l_Lean_setEnv___redArg(v_inst_1946_, v_a_1956_);
return v___x_1961_;
}
else
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_nat_dec_le(v___x_1958_, v___x_1958_);
if (v___x_1962_ == 0)
{
if (v___x_1960_ == 0)
{
lean_object* v___x_1963_; 
lean_dec_ref(v___f_1947_);
lean_dec_ref(v_deferred_1945_);
v___x_1963_ = l_Lean_setEnv___redArg(v_inst_1946_, v_a_1956_);
return v___x_1963_;
}
else
{
size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = lean_usize_of_nat(v___x_1958_);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1959_, v___f_1947_, v_deferred_1945_, v___x_1964_, v___x_1965_, v_a_1956_);
v___x_1967_ = l_Lean_setEnv___redArg(v_inst_1946_, v___x_1966_);
return v___x_1967_;
}
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1958_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1959_, v___f_1947_, v_deferred_1945_, v___x_1968_, v___x_1969_, v_a_1956_);
v___x_1971_ = l_Lean_setEnv___redArg(v_inst_1946_, v___x_1970_);
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2(uint8_t v___x_1972_, lean_object* v_docs_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_deferred_1976_, lean_object* v_inst_1977_, lean_object* v_toBind_1978_, lean_object* v_getEnv_1979_, lean_object* v_____do__lift_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v_size_1982_; lean_object* v___x_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___x_1986_; 
v___x_1981_ = l_Lean_getMainVersoModuleDocs(v_____do__lift_1980_);
v_size_1982_ = lean_ctor_get(v___x_1981_, 2);
lean_inc(v_size_1982_);
lean_dec_ref(v___x_1981_);
v___x_1983_ = lean_box(v___x_1972_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1984_, 0, v_size_1982_);
lean_closure_set(v___f_1984_, 1, v___x_1983_);
v___f_1985_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1985_, 0, v_docs_1973_);
lean_closure_set(v___f_1985_, 1, v_inst_1974_);
lean_closure_set(v___f_1985_, 2, v_inst_1975_);
lean_closure_set(v___f_1985_, 3, v_deferred_1976_);
lean_closure_set(v___f_1985_, 4, v_inst_1977_);
lean_closure_set(v___f_1985_, 5, v___f_1984_);
v___x_1986_ = lean_apply_4(v_toBind_1978_, lean_box(0), lean_box(0), v_getEnv_1979_, v___f_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed(lean_object* v___x_1987_, lean_object* v_docs_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_deferred_1991_, lean_object* v_inst_1992_, lean_object* v_toBind_1993_, lean_object* v_getEnv_1994_, lean_object* v_____do__lift_1995_){
_start:
{
uint8_t v___x_436__boxed_1996_; lean_object* v_res_1997_; 
v___x_436__boxed_1996_ = lean_unbox(v___x_1987_);
v_res_1997_ = l_Lean_addVersoModDocStringCore___redArg___lam__2(v___x_436__boxed_1996_, v_docs_1988_, v_inst_1989_, v_inst_1990_, v_deferred_1991_, v_inst_1992_, v_toBind_1993_, v_getEnv_1994_, v_____do__lift_1995_);
return v_res_1997_;
}
}
static lean_object* _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = ((lean_object*)(l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__0));
v___x_2000_ = l_Lean_stringToMessageData(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg___lam__3(lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_docs_2003_, lean_object* v_deferred_2004_, lean_object* v_inst_2005_, lean_object* v_toBind_2006_, lean_object* v_getEnv_2007_, lean_object* v_____do__lift_2008_){
_start:
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = l_Lean_getMainModuleDoc(v_____do__lift_2008_);
v___x_2010_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_2009_);
lean_dec_ref(v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v_getEnv_2007_);
lean_dec(v_toBind_2006_);
lean_dec_ref(v_inst_2005_);
lean_dec_ref(v_deferred_2004_);
lean_dec_ref(v_docs_2003_);
v___x_2011_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_2012_ = l_Lean_throwError___redArg(v_inst_2001_, v_inst_2002_, v___x_2011_);
return v___x_2012_;
}
else
{
lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(v___x_2010_);
lean_inc(v_getEnv_2007_);
lean_inc(v_toBind_2006_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2014_, 0, v___x_2013_);
lean_closure_set(v___f_2014_, 1, v_docs_2003_);
lean_closure_set(v___f_2014_, 2, v_inst_2001_);
lean_closure_set(v___f_2014_, 3, v_inst_2002_);
lean_closure_set(v___f_2014_, 4, v_deferred_2004_);
lean_closure_set(v___f_2014_, 5, v_inst_2005_);
lean_closure_set(v___f_2014_, 6, v_toBind_2006_);
lean_closure_set(v___f_2014_, 7, v_getEnv_2007_);
v___x_2015_ = lean_apply_4(v_toBind_2006_, lean_box(0), lean_box(0), v_getEnv_2007_, v___f_2014_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___redArg(lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_docs_2019_, lean_object* v_deferred_2020_){
_start:
{
lean_object* v_toBind_2021_; lean_object* v_getEnv_2022_; lean_object* v___f_2023_; lean_object* v___x_2024_; 
v_toBind_2021_ = lean_ctor_get(v_inst_2016_, 1);
lean_inc_n(v_toBind_2021_, 2);
v_getEnv_2022_ = lean_ctor_get(v_inst_2017_, 0);
lean_inc_n(v_getEnv_2022_, 2);
v___f_2023_ = lean_alloc_closure((void*)(l_Lean_addVersoModDocStringCore___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2023_, 0, v_inst_2016_);
lean_closure_set(v___f_2023_, 1, v_inst_2018_);
lean_closure_set(v___f_2023_, 2, v_docs_2019_);
lean_closure_set(v___f_2023_, 3, v_deferred_2020_);
lean_closure_set(v___f_2023_, 4, v_inst_2017_);
lean_closure_set(v___f_2023_, 5, v_toBind_2021_);
lean_closure_set(v___f_2023_, 6, v_getEnv_2022_);
v___x_2024_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v_getEnv_2022_, v___f_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore(lean_object* v_m_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_docs_2030_, lean_object* v_deferred_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_addVersoModDocStringCore___redArg(v_inst_2026_, v_inst_2027_, v_inst_2029_, v_docs_2030_, v_deferred_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___boxed(lean_object* v_m_2033_, lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_docs_2038_, lean_object* v_deferred_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_addVersoModDocStringCore(v_m_2033_, v_inst_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_docs_2038_, v_deferred_2039_);
lean_dec(v_inst_2036_);
return v_res_2040_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_box(1);
v___x_2042_ = l_Lean_MessageData_ofFormat(v___x_2041_);
return v___x_2042_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__2));
v___x_2047_ = l_Lean_MessageData_ofFormat(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
return v_x_2048_;
}
else
{
lean_object* v_head_2050_; lean_object* v_tail_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2073_; 
v_head_2050_ = lean_ctor_get(v_x_2049_, 0);
v_tail_2051_ = lean_ctor_get(v_x_2049_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_x_2049_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2053_ = v_x_2049_;
v_isShared_2054_ = v_isSharedCheck_2073_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_tail_2051_);
lean_inc(v_head_2050_);
lean_dec(v_x_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2073_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v_before_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2071_; 
v_before_2055_ = lean_ctor_get(v_head_2050_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_head_2050_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_head_2050_, 1);
lean_dec(v_unused_2072_);
v___x_2057_ = v_head_2050_;
v_isShared_2058_ = v_isSharedCheck_2071_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_before_2055_);
lean_dec(v_head_2050_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2071_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 7);
lean_ctor_set(v___x_2057_, 1, v___x_2059_);
lean_ctor_set(v___x_2057_, 0, v_x_2048_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_x_2048_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 7);
lean_ctor_set(v___x_2053_, 1, v___x_2062_);
lean_ctor_set(v___x_2053_, 0, v___x_2061_);
v___x_2064_ = v___x_2053_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = l_Lean_MessageData_ofSyntax(v_before_2055_);
v___x_2066_ = l_Lean_indentD(v___x_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v_x_2048_ = v___x_2067_;
v_x_2049_ = v_tail_2051_;
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
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__1));
v___x_2078_ = l_Lean_MessageData_ofFormat(v___x_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(lean_object* v_msgData_2079_, lean_object* v_macroStack_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2083_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2081_);
v___x_2084_ = l_Lean_Elab_pp_macroStack;
v___x_2085_ = l_Lean_Option_get___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__4(v___x_2083_, v___x_2084_);
lean_dec_ref(v___x_2083_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v_macroStack_2080_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_msgData_2079_);
return v___x_2086_;
}
else
{
if (lean_obj_tag(v_macroStack_2080_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_msgData_2079_);
return v___x_2087_;
}
else
{
lean_object* v_head_2088_; lean_object* v_after_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2104_; 
v_head_2088_ = lean_ctor_get(v_macroStack_2080_, 0);
lean_inc(v_head_2088_);
v_after_2089_ = lean_ctor_get(v_head_2088_, 1);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_head_2088_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_head_2088_, 0);
lean_dec(v_unused_2105_);
v___x_2091_ = v_head_2088_;
v_isShared_2092_ = v_isSharedCheck_2104_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_after_2089_);
lean_dec(v_head_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2104_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2092_ == 0)
{
lean_ctor_set_tag(v___x_2091_, 7);
lean_ctor_set(v___x_2091_, 1, v___x_2093_);
lean_ctor_set(v___x_2091_, 0, v_msgData_2079_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_msgData_2079_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_msgData_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2096_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___closed__2);
v___x_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = l_Lean_MessageData_ofSyntax(v_after_2089_);
v___x_2099_ = l_Lean_indentD(v___x_2098_);
v_msgData_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2100_, 0, v___x_2097_);
lean_ctor_set(v_msgData_2100_, 1, v___x_2099_);
v___x_2101_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2_spec__3(v_msgData_2100_, v_macroStack_2080_);
v___x_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2106_, lean_object* v_macroStack_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2106_, v_macroStack_2107_, v___y_2108_);
lean_dec_ref(v___y_2108_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(lean_object* v_msg_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_ref_2119_; lean_object* v_macroStack_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2133_; 
v_ref_2119_ = lean_ctor_get(v___y_2116_, 2);
v_macroStack_2120_ = lean_ctor_get(v___y_2112_, 1);
v___x_2121_ = l_Lean_Elab_getBetterRef(v_ref_2119_, v_macroStack_2120_);
v___x_2122_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2_spec__3(v_msg_2111_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
lean_inc(v_macroStack_2120_);
v___x_2124_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_a_2123_, v_macroStack_2120_, v___y_2116_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2133_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2121_);
lean_ctor_set(v___x_2129_, 1, v_a_2125_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 1);
lean_ctor_set(v___x_2127_, 0, v___x_2129_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg___boxed(lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0(lean_object* v___x_2143_, lean_object* v___x_2144_, lean_object* v_s_2145_){
_start:
{
lean_object* v_addEntryFn_2146_; lean_object* v_importedEntries_2147_; lean_object* v_state_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2156_; 
v_addEntryFn_2146_ = lean_ctor_get(v___x_2143_, 3);
lean_inc(v_addEntryFn_2146_);
lean_dec_ref(v___x_2143_);
v_importedEntries_2147_ = lean_ctor_get(v_s_2145_, 0);
v_state_2148_ = lean_ctor_get(v_s_2145_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_s_2145_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2150_ = v_s_2145_;
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_state_2148_);
lean_inc(v_importedEntries_2147_);
lean_dec(v_s_2145_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2156_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_state_2152_; lean_object* v___x_2154_; 
v_state_2152_ = lean_apply_2(v_addEntryFn_2146_, v_state_2148_, v___x_2144_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_state_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_importedEntries_2147_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_state_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(lean_object* v_declName_2157_, lean_object* v_as_2158_, size_t v_i_2159_, size_t v_stop_2160_, lean_object* v_b_2161_){
_start:
{
lean_object* v___y_2163_; uint8_t v___x_2167_; 
v___x_2167_ = lean_usize_dec_eq(v_i_2159_, v_stop_2160_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_index_2169_; lean_object* v_sourceString_2170_; lean_object* v_imports_2171_; lean_object* v_currNamespace_2172_; lean_object* v_openDecls_2173_; lean_object* v_options_2174_; lean_object* v_check_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2193_; 
v___x_2168_ = lean_array_uget(v_as_2158_, v_i_2159_);
v_index_2169_ = lean_ctor_get(v___x_2168_, 1);
v_sourceString_2170_ = lean_ctor_get(v___x_2168_, 2);
v_imports_2171_ = lean_ctor_get(v___x_2168_, 3);
v_currNamespace_2172_ = lean_ctor_get(v___x_2168_, 4);
v_openDecls_2173_ = lean_ctor_get(v___x_2168_, 5);
v_options_2174_ = lean_ctor_get(v___x_2168_, 6);
v_check_2175_ = lean_ctor_get(v___x_2168_, 7);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2193_ == 0)
{
lean_object* v_unused_2194_; 
v_unused_2194_ = lean_ctor_get(v___x_2168_, 0);
lean_dec(v_unused_2194_);
v___x_2177_ = v___x_2168_;
v_isShared_2178_ = v_isSharedCheck_2193_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_check_2175_);
lean_inc(v_options_2174_);
lean_inc(v_openDecls_2173_);
lean_inc(v_currNamespace_2172_);
lean_inc(v_imports_2171_);
lean_inc(v_sourceString_2170_);
lean_inc(v_index_2169_);
lean_dec(v___x_2168_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2193_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v_toEnvExtension_2180_; lean_object* v_asyncMode_2181_; uint8_t v_logWrites_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2179_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_2180_ = lean_ctor_get(v___x_2179_, 0);
v_asyncMode_2181_ = lean_ctor_get(v_toEnvExtension_2180_, 2);
v_logWrites_2182_ = lean_ctor_get_uint8(v_toEnvExtension_2180_, sizeof(void*)*6);
lean_inc(v_declName_2157_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_declName_2157_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2183_);
v___x_2185_ = v___x_2177_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_index_2169_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_sourceString_2170_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_imports_2171_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v_currNamespace_2172_);
lean_ctor_set(v_reuseFailAlloc_2192_, 5, v_openDecls_2173_);
lean_ctor_set(v_reuseFailAlloc_2192_, 6, v_options_2174_);
lean_ctor_set(v_reuseFailAlloc_2192_, 7, v_check_2175_);
v___x_2185_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___f_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___f_2186_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2186_, 0, v___x_2179_);
lean_closure_set(v___f_2186_, 1, v___x_2185_);
v___x_2187_ = lean_box(0);
v___x_2188_ = 1;
if (v_logWrites_2182_ == 0)
{
lean_object* v___x_2189_; 
lean_inc_ref(v_toEnvExtension_2180_);
v___x_2189_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2180_, v_b_2161_, v___f_2186_, v_asyncMode_2181_, v___x_2187_, v___x_2188_);
v___y_2163_ = v___x_2189_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_inc_ref_n(v_toEnvExtension_2180_, 2);
v___x_2190_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2180_, v_b_2161_);
lean_dec_ref(v_b_2161_);
v___x_2191_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2180_, v___x_2190_, v___f_2186_, v_asyncMode_2181_, v___x_2187_, v___x_2188_);
v___y_2163_ = v___x_2191_;
goto v___jp_2162_;
}
}
}
}
else
{
lean_dec(v_declName_2157_);
return v_b_2161_;
}
v___jp_2162_:
{
size_t v___x_2164_; size_t v___x_2165_; 
v___x_2164_ = ((size_t)1ULL);
v___x_2165_ = lean_usize_add(v_i_2159_, v___x_2164_);
v_i_2159_ = v___x_2165_;
v_b_2161_ = v___y_2163_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___boxed(lean_object* v_declName_2195_, lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_stop_2198_, lean_object* v_b_2199_){
_start:
{
size_t v_i_boxed_2200_; size_t v_stop_boxed_2201_; lean_object* v_res_2202_; 
v_i_boxed_2200_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_stop_boxed_2201_ = lean_unbox_usize(v_stop_2198_);
lean_dec(v_stop_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2195_, v_as_2196_, v_i_boxed_2200_, v_stop_boxed_2201_, v_b_2199_);
lean_dec_ref(v_as_2196_);
return v_res_2202_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_parseVersoDocString_spec__0_spec__0___closed__0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__0);
v___x_2208_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_ctor_set(v___x_2208_, 3, v___x_2207_);
lean_ctor_set(v___x_2208_, 4, v___x_2207_);
lean_ctor_set(v___x_2208_, 5, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(lean_object* v_declName_2209_, lean_object* v_docs_2210_, lean_object* v_deferred_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; uint8_t v___x_2251_; 
v___x_2251_ = l_Lean_Name_isAnonymous(v_declName_2209_);
if (v___x_2251_ == 0)
{
uint8_t v___x_2252_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___x_2274_; lean_object* v_env_2275_; lean_object* v___x_2276_; 
v___x_2252_ = 1;
v___x_2274_ = lean_st_ref_get(v___y_2217_);
v_env_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc_ref(v_env_2275_);
lean_dec(v___x_2274_);
v___x_2276_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2275_, v_declName_2209_);
lean_dec_ref(v_env_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
v___y_2254_ = v___y_2215_;
v___y_2255_ = v___y_2217_;
goto v___jp_2253_;
}
else
{
lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2290_; 
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2290_ == 0)
{
lean_object* v_unused_2291_; 
v_unused_2291_ = lean_ctor_get(v___x_2276_, 0);
lean_dec(v_unused_2291_);
v___x_2278_ = v___x_2276_;
v_isShared_2279_ = v_isSharedCheck_2290_;
goto v_resetjp_2277_;
}
else
{
lean_dec(v___x_2276_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2290_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
if (v___x_2251_ == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec_ref(v_docs_2210_);
v___x_2280_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2209_, v___x_2252_);
v___x_2282_ = lean_string_append(v___x_2280_, v___x_2281_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2284_ = lean_string_append(v___x_2282_, v___x_2283_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 3);
lean_ctor_set(v___x_2278_, 0, v___x_2284_);
v___x_2286_ = v___x_2278_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = l_Lean_MessageData_ofFormat(v___x_2286_);
v___x_2288_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2287_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2288_;
}
}
else
{
lean_del_object(v___x_2278_);
v___y_2254_ = v___y_2215_;
v___y_2255_ = v___y_2217_;
goto v___jp_2253_;
}
}
}
v___jp_2253_:
{
lean_object* v___x_2256_; lean_object* v_env_2257_; lean_object* v_nextMacroScope_2258_; lean_object* v_ngen_2259_; lean_object* v_auxDeclNGen_2260_; lean_object* v_traceState_2261_; lean_object* v_recordedDeps_2262_; lean_object* v_messages_2263_; lean_object* v_infoState_2264_; lean_object* v_snapshotTasks_2265_; lean_object* v___x_2266_; lean_object* v_env_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2256_ = lean_st_ref_take(v___y_2255_);
v_env_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc_ref(v_env_2257_);
v_nextMacroScope_2258_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_nextMacroScope_2258_);
v_ngen_2259_ = lean_ctor_get(v___x_2256_, 2);
lean_inc_ref(v_ngen_2259_);
v_auxDeclNGen_2260_ = lean_ctor_get(v___x_2256_, 3);
lean_inc_ref(v_auxDeclNGen_2260_);
v_traceState_2261_ = lean_ctor_get(v___x_2256_, 4);
lean_inc_ref(v_traceState_2261_);
v_recordedDeps_2262_ = lean_ctor_get(v___x_2256_, 6);
lean_inc_ref(v_recordedDeps_2262_);
v_messages_2263_ = lean_ctor_get(v___x_2256_, 7);
lean_inc_ref(v_messages_2263_);
v_infoState_2264_ = lean_ctor_get(v___x_2256_, 8);
lean_inc_ref(v_infoState_2264_);
v_snapshotTasks_2265_ = lean_ctor_get(v___x_2256_, 9);
lean_inc_ref(v_snapshotTasks_2265_);
lean_dec(v___x_2256_);
v___x_2266_ = l_Lean_versoDocStringExt;
lean_inc(v_declName_2209_);
v_env_2267_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2266_, v_env_2257_, v_declName_2209_, v_docs_2210_, v___x_2252_);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_array_get_size(v_deferred_2211_);
v___x_2270_ = lean_nat_dec_lt(v___x_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec(v_declName_2209_);
v___y_2220_ = v_ngen_2259_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v_snapshotTasks_2265_;
v___y_2223_ = v_traceState_2261_;
v___y_2224_ = v___y_2254_;
v___y_2225_ = v_nextMacroScope_2258_;
v___y_2226_ = v_infoState_2264_;
v___y_2227_ = v_recordedDeps_2262_;
v___y_2228_ = v_auxDeclNGen_2260_;
v___y_2229_ = v_messages_2263_;
v___y_2230_ = v_env_2267_;
goto v___jp_2219_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2269_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0(v_declName_2209_, v_deferred_2211_, v___x_2271_, v___x_2272_, v_env_2267_);
v___y_2220_ = v_ngen_2259_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v_snapshotTasks_2265_;
v___y_2223_ = v_traceState_2261_;
v___y_2224_ = v___y_2254_;
v___y_2225_ = v_nextMacroScope_2258_;
v___y_2226_ = v_infoState_2264_;
v___y_2227_ = v_recordedDeps_2262_;
v___y_2228_ = v_auxDeclNGen_2260_;
v___y_2229_ = v_messages_2263_;
v___y_2230_ = v___x_2273_;
goto v___jp_2219_;
}
}
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_docs_2210_);
lean_dec(v_declName_2209_);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
v___jp_2219_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_mctx_2235_; lean_object* v_zetaDeltaFVarIds_2236_; lean_object* v_postponed_2237_; lean_object* v_diag_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2249_; 
v___x_2231_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_2232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2232_, 0, v___y_2230_);
lean_ctor_set(v___x_2232_, 1, v___y_2225_);
lean_ctor_set(v___x_2232_, 2, v___y_2220_);
lean_ctor_set(v___x_2232_, 3, v___y_2228_);
lean_ctor_set(v___x_2232_, 4, v___y_2223_);
lean_ctor_set(v___x_2232_, 5, v___x_2231_);
lean_ctor_set(v___x_2232_, 6, v___y_2227_);
lean_ctor_set(v___x_2232_, 7, v___y_2229_);
lean_ctor_set(v___x_2232_, 8, v___y_2226_);
lean_ctor_set(v___x_2232_, 9, v___y_2222_);
v___x_2233_ = lean_st_ref_put(v___y_2221_, v___x_2232_);
v___x_2234_ = lean_st_ref_take(v___y_2224_);
v_mctx_2235_ = lean_ctor_get(v___x_2234_, 0);
v_zetaDeltaFVarIds_2236_ = lean_ctor_get(v___x_2234_, 2);
v_postponed_2237_ = lean_ctor_get(v___x_2234_, 3);
v_diag_2238_ = lean_ctor_get(v___x_2234_, 4);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2234_, 1);
lean_dec(v_unused_2250_);
v___x_2240_ = v___x_2234_;
v_isShared_2241_ = v_isSharedCheck_2249_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_diag_2238_);
lean_inc(v_postponed_2237_);
lean_inc(v_zetaDeltaFVarIds_2236_);
lean_inc(v_mctx_2235_);
lean_dec(v___x_2234_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2249_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2242_ = lean_box(0);
v___x_2243_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v___x_2243_);
v___x_2245_ = v___x_2240_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_mctx_2235_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2248_, 2, v_zetaDeltaFVarIds_2236_);
lean_ctor_set(v_reuseFailAlloc_2248_, 3, v_postponed_2237_);
lean_ctor_set(v_reuseFailAlloc_2248_, 4, v_diag_2238_);
v___x_2245_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = lean_st_ref_put(v___y_2224_, v___x_2245_);
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2242_);
return v___x_2247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___boxed(lean_object* v_declName_2294_, lean_object* v_docs_2295_, lean_object* v_deferred_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2294_, v_docs_2295_, v_deferred_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_deferred_2296_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString(lean_object* v_declName_2305_, lean_object* v_binders_2306_, lean_object* v_docComment_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___x_2335_; lean_object* v_env_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_st_ref_get(v_a_2313_);
v_env_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_ref(v_env_2336_);
lean_dec(v___x_2335_);
v___x_2337_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2336_, v_declName_2305_);
lean_dec_ref(v_env_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
v___y_2316_ = v_a_2308_;
v___y_2317_ = v_a_2309_;
v___y_2318_ = v_a_2310_;
v___y_2319_ = v_a_2311_;
v___y_2320_ = v_a_2312_;
v___y_2321_ = v_a_2313_;
goto v___jp_2315_;
}
else
{
lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_binders_2306_);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; 
v_unused_2353_ = lean_ctor_get(v___x_2337_, 0);
lean_dec(v_unused_2353_);
v___x_2339_ = v___x_2337_;
v_isShared_2340_ = v_isSharedCheck_2352_;
goto v_resetjp_2338_;
}
else
{
lean_dec(v___x_2337_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2352_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2341_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2342_ = 1;
v___x_2343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2305_, v___x_2342_);
v___x_2344_ = lean_string_append(v___x_2341_, v___x_2343_);
lean_dec_ref(v___x_2343_);
v___x_2345_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2346_ = lean_string_append(v___x_2344_, v___x_2345_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 3);
lean_ctor_set(v___x_2339_, 0, v___x_2346_);
v___x_2348_ = v___x_2339_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = l_Lean_MessageData_ofFormat(v___x_2348_);
v___x_2350_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2349_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_);
return v___x_2350_;
}
}
}
v___jp_2315_:
{
lean_object* v___x_2322_; 
lean_inc(v_declName_2305_);
v___x_2322_ = l_Lean_versoDocString(v_declName_2305_, v_binders_2306_, v_docComment_2307_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_toVersoDocString_2324_; lean_object* v_deferredChecks_2325_; lean_object* v___x_2326_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v_toVersoDocString_2324_ = lean_ctor_get(v_a_2323_, 0);
lean_inc_ref(v_toVersoDocString_2324_);
v_deferredChecks_2325_ = lean_ctor_get(v_a_2323_, 1);
lean_inc_ref(v_deferredChecks_2325_);
lean_dec(v_a_2323_);
v___x_2326_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2305_, v_toVersoDocString_2324_, v_deferredChecks_2325_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec_ref(v_deferredChecks_2325_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_declName_2305_);
v_a_2327_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2322_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2322_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocString___boxed(lean_object* v_declName_2354_, lean_object* v_binders_2355_, lean_object* v_docComment_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_addVersoDocString(v_declName_2354_, v_binders_2355_, v_docComment_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_docComment_2356_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(lean_object* v_00_u03b1_2365_, lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1(v_00_u03b1_2375_, v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(lean_object* v_msgData_2385_, lean_object* v_macroStack_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___redArg(v_msgData_2385_, v_macroStack_2386_, v___y_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2___boxed(lean_object* v_msgData_2395_, lean_object* v_macroStack_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_addVersoDocString_spec__1_spec__2(v_msgData_2395_, v_macroStack_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString(lean_object* v_declName_2405_, lean_object* v_docComment_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___x_2434_; lean_object* v_env_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_st_ref_get(v_a_2412_);
v_env_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc_ref(v_env_2435_);
lean_dec(v___x_2434_);
v___x_2436_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2435_, v_declName_2405_);
lean_dec_ref(v_env_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
v___y_2415_ = v_a_2407_;
v___y_2416_ = v_a_2408_;
v___y_2417_ = v_a_2409_;
v___y_2418_ = v_a_2410_;
v___y_2419_ = v_a_2411_;
v___y_2420_ = v_a_2412_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v_docComment_2406_);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; 
v_unused_2452_ = lean_ctor_get(v___x_2436_, 0);
lean_dec(v_unused_2452_);
v___x_2438_ = v___x_2436_;
v_isShared_2439_ = v_isSharedCheck_2451_;
goto v_resetjp_2437_;
}
else
{
lean_dec(v___x_2436_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2451_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2440_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__0));
v___x_2441_ = 1;
v___x_2442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_2405_, v___x_2441_);
v___x_2443_ = lean_string_append(v___x_2440_, v___x_2442_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = ((lean_object*)(l_Lean_addVersoDocStringCore___redArg___lam__4___closed__1));
v___x_2445_ = lean_string_append(v___x_2443_, v___x_2444_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 3);
lean_ctor_set(v___x_2438_, 0, v___x_2445_);
v___x_2447_ = v___x_2438_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = l_Lean_MessageData_ofFormat(v___x_2447_);
v___x_2449_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2448_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
return v___x_2449_;
}
}
}
v___jp_2414_:
{
lean_object* v___x_2421_; 
lean_inc(v_declName_2405_);
v___x_2421_ = l_Lean_versoDocStringFromString(v_declName_2405_, v_docComment_2406_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_toVersoDocString_2423_; lean_object* v_deferredChecks_2424_; lean_object* v___x_2425_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v_toVersoDocString_2423_ = lean_ctor_get(v_a_2422_, 0);
lean_inc_ref(v_toVersoDocString_2423_);
v_deferredChecks_2424_ = lean_ctor_get(v_a_2422_, 1);
lean_inc_ref(v_deferredChecks_2424_);
lean_dec(v_a_2422_);
v___x_2425_ = l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0(v_declName_2405_, v_toVersoDocString_2423_, v_deferredChecks_2424_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec_ref(v_deferredChecks_2424_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_declName_2405_);
v_a_2426_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2421_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2421_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoDocStringFromString___boxed(lean_object* v_declName_2453_, lean_object* v_docComment_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_addVersoDocStringFromString(v_declName_2453_, v_docComment_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2463_, lean_object* v_msgData_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
uint8_t v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = 2;
v___x_2471_ = 0;
v___x_2472_ = l_Lean_logAt___at___00__private_Lean_DocString_Add_0__Lean_execVersoBlocks_spec__2___redArg(v_ref_2463_, v_msgData_2464_, v___x_2470_, v___x_2471_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2473_, lean_object* v_msgData_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2473_, v_msgData_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v_ref_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(lean_object* v___y_2481_, lean_object* v_str_2482_, lean_object* v_as_2483_, size_t v_sz_2484_, size_t v_i_2485_, lean_object* v_b_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_a_2495_; uint8_t v___x_2499_; 
v___x_2499_ = lean_usize_dec_lt(v_i_2485_, v_sz_2484_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v_b_2486_);
return v___x_2500_;
}
else
{
lean_object* v_a_2501_; lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v_start_2504_; lean_object* v_stop_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2525_; 
v_a_2501_ = lean_array_uget_borrowed(v_as_2483_, v_i_2485_);
v_fst_2502_ = lean_ctor_get(v_a_2501_, 0);
lean_inc(v_fst_2502_);
v_snd_2503_ = lean_ctor_get(v_a_2501_, 1);
v_start_2504_ = lean_ctor_get(v_fst_2502_, 0);
v_stop_2505_ = lean_ctor_get(v_fst_2502_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_fst_2502_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2507_ = v_fst_2502_;
v_isShared_2508_ = v_isSharedCheck_2525_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_stop_2505_);
lean_inc(v_start_2504_);
lean_dec(v_fst_2502_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2525_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_box(0);
if (lean_obj_tag(v___y_2481_) == 1)
{
lean_object* v_val_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v_val_2510_ = lean_ctor_get(v___y_2481_, 0);
v___x_2511_ = lean_nat_add(v_val_2510_, v_start_2504_);
v___x_2512_ = lean_nat_add(v_val_2510_, v_stop_2505_);
v___x_2513_ = 0;
v___x_2514_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2514_, 0, v___x_2511_);
lean_ctor_set(v___x_2514_, 1, v___x_2512_);
lean_ctor_set_uint8(v___x_2514_, sizeof(void*)*2, v___x_2513_);
v___x_2515_ = lean_string_utf8_extract(v_str_2482_, v_start_2504_, v_stop_2505_);
lean_dec(v_stop_2505_);
lean_dec(v_start_2504_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set_tag(v___x_2507_, 2);
lean_ctor_set(v___x_2507_, 1, v___x_2515_);
lean_ctor_set(v___x_2507_, 0, v___x_2514_);
v___x_2517_ = v___x_2507_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_inc(v_snd_2503_);
v___x_2518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_snd_2503_);
v___x_2519_ = l_Lean_MessageData_ofFormat(v___x_2518_);
v___x_2520_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v___x_2517_, v___x_2519_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec_ref(v___x_2517_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_dec_ref_known(v___x_2520_, 1);
v_a_2495_ = v___x_2509_;
goto v___jp_2494_;
}
else
{
return v___x_2520_;
}
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_del_object(v___x_2507_);
lean_dec(v_stop_2505_);
lean_dec(v_start_2504_);
lean_inc(v_snd_2503_);
v___x_2522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_snd_2503_);
v___x_2523_ = l_Lean_MessageData_ofFormat(v___x_2522_);
v___x_2524_ = l_Lean_logError___at___00Lean_versoDocStringOfText_spec__0(v___x_2523_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_dec_ref_known(v___x_2524_, 1);
v_a_2495_ = v___x_2509_;
goto v___jp_2494_;
}
else
{
return v___x_2524_;
}
}
}
}
v___jp_2494_:
{
size_t v___x_2496_; size_t v___x_2497_; 
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_add(v_i_2485_, v___x_2496_);
v_i_2485_ = v___x_2497_;
v_b_2486_ = v_a_2495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2___boxed(lean_object* v___y_2526_, lean_object* v_str_2527_, lean_object* v_as_2528_, lean_object* v_sz_2529_, lean_object* v_i_2530_, lean_object* v_b_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
size_t v_sz_boxed_2539_; size_t v_i_boxed_2540_; lean_object* v_res_2541_; 
v_sz_boxed_2539_ = lean_unbox_usize(v_sz_2529_);
lean_dec(v_sz_2529_);
v_i_boxed_2540_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_res_2541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2526_, v_str_2527_, v_as_2528_, v_sz_boxed_2539_, v_i_boxed_2540_, v_b_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec_ref(v_as_2528_);
lean_dec_ref(v_str_2527_);
lean_dec(v___y_2526_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(lean_object* v_docstring_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_str_2550_; lean_object* v___y_2552_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_str_2550_ = l_Lean_TSyntax_getDocString(v_docstring_2542_);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = l_Lean_Syntax_getArg(v_docstring_2542_, v___x_2567_);
v___x_2569_ = l_Lean_Syntax_getHeadInfo_x3f(v___x_2568_);
lean_dec(v___x_2568_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_box(0);
v___y_2552_ = v___x_2570_;
goto v___jp_2551_;
}
else
{
lean_object* v_val_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; 
v_val_2571_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2571_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2572_ = 0;
v___x_2573_ = l_Lean_SourceInfo_getPos_x3f(v_val_2571_, v___x_2572_);
lean_dec(v_val_2571_);
v___y_2552_ = v___x_2573_;
goto v___jp_2551_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v_fst_2554_; lean_object* v___x_2555_; size_t v_sz_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
lean_inc_ref(v_str_2550_);
v___x_2553_ = l_Lean_rewriteManualLinksCore(v_str_2550_);
v_fst_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_fst_2554_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_box(0);
v_sz_2556_ = lean_array_size(v_fst_2554_);
v___x_2557_ = ((size_t)0ULL);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__2(v___y_2552_, v_str_2550_, v_fst_2554_, v_sz_2556_, v___x_2557_, v___x_2555_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v_fst_2554_);
lean_dec_ref(v_str_2550_);
lean_dec(v___y_2552_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2558_, 0);
lean_dec(v_unused_2566_);
v___x_2560_ = v___x_2558_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_dec(v___x_2558_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2555_);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2555_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
return v___x_2558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0___boxed(lean_object* v_docstring_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docstring_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v_docstring_2574_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_2583_, lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_toCold_2592_; lean_object* v_currRecDepth_2593_; lean_object* v_ref_2594_; uint16_t v_optionFlags_2595_; uint8_t v_suppressElabErrors_2596_; uint8_t v_isRecordingDeps_2597_; lean_object* v_ref_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_toCold_2592_ = lean_ctor_get(v___y_2589_, 0);
v_currRecDepth_2593_ = lean_ctor_get(v___y_2589_, 1);
v_ref_2594_ = lean_ctor_get(v___y_2589_, 2);
v_optionFlags_2595_ = lean_ctor_get_uint16(v___y_2589_, sizeof(void*)*3);
v_suppressElabErrors_2596_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2597_ = lean_ctor_get_uint8(v___y_2589_, sizeof(void*)*3 + 3);
v_ref_2598_ = l_Lean_replaceRef(v_ref_2583_, v_ref_2594_);
lean_inc(v_currRecDepth_2593_);
lean_inc_ref(v_toCold_2592_);
v___x_2599_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2599_, 0, v_toCold_2592_);
lean_ctor_set(v___x_2599_, 1, v_currRecDepth_2593_);
lean_ctor_set(v___x_2599_, 2, v_ref_2598_);
lean_ctor_set_uint16(v___x_2599_, sizeof(void*)*3, v_optionFlags_2595_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*3 + 2, v_suppressElabErrors_2596_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*3 + 3, v_isRecordingDeps_2597_);
v___x_2600_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v_msg_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___x_2599_, v___y_2590_);
lean_dec_ref_known(v___x_2599_, 3);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_2601_, lean_object* v_msg_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2601_, v_msg_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v_ref_2601_);
return v_res_2610_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__0));
v___x_2613_ = l_Lean_stringToMessageData(v___x_2612_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(lean_object* v_stx_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_unsigned_to_nat(1u);
v___x_2630_ = l_Lean_Syntax_getArg(v_stx_2615_, v___x_2629_);
if (lean_obj_tag(v___x_2630_) == 1)
{
lean_object* v_kind_2631_; 
v_kind_2631_ = lean_ctor_get(v___x_2630_, 1);
lean_inc(v_kind_2631_);
if (lean_obj_tag(v_kind_2631_) == 1)
{
lean_object* v_pre_2632_; 
v_pre_2632_ = lean_ctor_get(v_kind_2631_, 0);
lean_inc(v_pre_2632_);
if (lean_obj_tag(v_pre_2632_) == 1)
{
lean_object* v_pre_2633_; 
v_pre_2633_ = lean_ctor_get(v_pre_2632_, 0);
lean_inc(v_pre_2633_);
if (lean_obj_tag(v_pre_2633_) == 1)
{
lean_object* v_pre_2634_; 
v_pre_2634_ = lean_ctor_get(v_pre_2633_, 0);
lean_inc(v_pre_2634_);
if (lean_obj_tag(v_pre_2634_) == 1)
{
lean_object* v_pre_2635_; 
v_pre_2635_ = lean_ctor_get(v_pre_2634_, 0);
if (lean_obj_tag(v_pre_2635_) == 0)
{
lean_object* v_args_2636_; lean_object* v_str_2637_; lean_object* v_str_2638_; lean_object* v_str_2639_; lean_object* v_str_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v_args_2636_ = lean_ctor_get(v___x_2630_, 2);
lean_inc_ref(v_args_2636_);
lean_dec_ref_known(v___x_2630_, 3);
v_str_2637_ = lean_ctor_get(v_kind_2631_, 1);
lean_inc_ref(v_str_2637_);
lean_dec_ref_known(v_kind_2631_, 2);
v_str_2638_ = lean_ctor_get(v_pre_2632_, 1);
lean_inc_ref(v_str_2638_);
lean_dec_ref_known(v_pre_2632_, 2);
v_str_2639_ = lean_ctor_get(v_pre_2633_, 1);
lean_inc_ref(v_str_2639_);
lean_dec_ref_known(v_pre_2633_, 2);
v_str_2640_ = lean_ctor_get(v_pre_2634_, 1);
lean_inc_ref(v_str_2640_);
lean_dec_ref_known(v_pre_2634_, 2);
v___x_2641_ = ((lean_object*)(l_Lean_versoDocString___closed__0));
v___x_2642_ = lean_string_dec_eq(v_str_2640_, v___x_2641_);
lean_dec_ref(v_str_2640_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v_str_2639_);
lean_dec_ref(v_str_2638_);
lean_dec_ref(v_str_2637_);
lean_dec_ref(v_args_2636_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_versoDocString___closed__1));
v___x_2644_ = lean_string_dec_eq(v_str_2639_, v___x_2643_);
lean_dec_ref(v_str_2639_);
if (v___x_2644_ == 0)
{
lean_dec_ref(v_str_2638_);
lean_dec_ref(v_str_2637_);
lean_dec_ref(v_args_2636_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_versoDocString___closed__2));
v___x_2646_ = lean_string_dec_eq(v_str_2638_, v___x_2645_);
lean_dec_ref(v_str_2638_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v_str_2637_);
lean_dec_ref(v_args_2636_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__2));
v___x_2648_ = lean_string_dec_eq(v_str_2637_, v___x_2647_);
lean_dec_ref(v_str_2637_);
if (v___x_2648_ == 0)
{
lean_dec_ref(v_args_2636_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = lean_array_get_size(v_args_2636_);
v___x_2650_ = lean_unsigned_to_nat(2u);
v___x_2651_ = lean_nat_dec_eq(v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
lean_dec_ref(v_args_2636_);
goto v___jp_2623_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = lean_array_fget(v_args_2636_, v___x_2652_);
lean_dec_ref(v_args_2636_);
if (lean_obj_tag(v___x_2653_) == 2)
{
lean_object* v_val_2654_; lean_object* v___x_2655_; 
lean_dec(v_stx_2615_);
v_val_2654_ = lean_ctor_get(v___x_2653_, 1);
lean_inc_ref(v_val_2654_);
lean_dec_ref_known(v___x_2653_, 2);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_val_2654_);
return v___x_2655_;
}
else
{
lean_dec(v___x_2653_);
goto v___jp_2623_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2634_, 2);
lean_dec_ref_known(v_pre_2633_, 2);
lean_dec_ref_known(v_pre_2632_, 2);
lean_dec_ref_known(v_kind_2631_, 2);
lean_dec_ref_known(v___x_2630_, 3);
goto v___jp_2623_;
}
}
else
{
lean_dec(v_pre_2634_);
lean_dec_ref_known(v_pre_2633_, 2);
lean_dec_ref_known(v_pre_2632_, 2);
lean_dec_ref_known(v_kind_2631_, 2);
lean_dec_ref_known(v___x_2630_, 3);
goto v___jp_2623_;
}
}
else
{
lean_dec(v_pre_2633_);
lean_dec_ref_known(v_pre_2632_, 2);
lean_dec_ref_known(v_kind_2631_, 2);
lean_dec_ref_known(v___x_2630_, 3);
goto v___jp_2623_;
}
}
else
{
lean_dec_ref_known(v_kind_2631_, 2);
lean_dec(v_pre_2632_);
lean_dec_ref_known(v___x_2630_, 3);
goto v___jp_2623_;
}
}
else
{
lean_dec(v_kind_2631_);
lean_dec_ref_known(v___x_2630_, 3);
goto v___jp_2623_;
}
}
else
{
lean_dec(v___x_2630_);
goto v___jp_2623_;
}
v___jp_2623_:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2624_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1, &l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___closed__1);
lean_inc(v_stx_2615_);
v___x_2625_ = l_Lean_MessageData_ofSyntax(v_stx_2615_);
v___x_2626_ = l_Lean_indentD(v___x_2625_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2624_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_stx_2615_, v___x_2627_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v_stx_2615_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1___boxed(lean_object* v_stx_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_stx_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(lean_object* v_declName_2665_, lean_object* v_docComment_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_2674_; 
v___x_2674_ = l_Lean_Name_isAnonymous(v_declName_2665_);
if (v___x_2674_ == 0)
{
uint8_t v___x_2675_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; lean_object* v___y_2682_; lean_object* v___x_2740_; lean_object* v_env_2741_; lean_object* v___x_2742_; 
v___x_2675_ = 1;
v___x_2740_ = lean_st_ref_get(v___y_2672_);
v_env_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_env_2741_);
lean_dec(v___x_2740_);
v___x_2742_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2741_, v_declName_2665_);
lean_dec_ref(v_env_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
v___y_2677_ = v___y_2667_;
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
goto v___jp_2676_;
}
else
{
lean_dec_ref_known(v___x_2742_, 1);
if (v___x_2674_ == 0)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v_docComment_2666_);
v___x_2743_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__1, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__1_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__1);
v___x_2744_ = l_Lean_MessageData_ofConstName(v_declName_2665_, v___x_2674_);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2743_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_2747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v___x_2748_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_2747_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2748_;
}
else
{
v___y_2677_ = v___y_2667_;
v___y_2678_ = v___y_2668_;
v___y_2679_ = v___y_2669_;
v___y_2680_ = v___y_2670_;
v___y_2681_ = v___y_2671_;
v___y_2682_ = v___y_2672_;
goto v___jp_2676_;
}
}
v___jp_2676_:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0(v_docComment_2666_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v___x_2684_; 
lean_dec_ref_known(v___x_2683_, 1);
v___x_2684_ = l_Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1(v_docComment_2666_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2731_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2731_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2731_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v_env_2690_; lean_object* v_nextMacroScope_2691_; lean_object* v_ngen_2692_; lean_object* v_auxDeclNGen_2693_; lean_object* v_traceState_2694_; lean_object* v_recordedDeps_2695_; lean_object* v_messages_2696_; lean_object* v_infoState_2697_; lean_object* v_snapshotTasks_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2729_; 
v___x_2689_ = lean_st_ref_take(v___y_2682_);
v_env_2690_ = lean_ctor_get(v___x_2689_, 0);
v_nextMacroScope_2691_ = lean_ctor_get(v___x_2689_, 1);
v_ngen_2692_ = lean_ctor_get(v___x_2689_, 2);
v_auxDeclNGen_2693_ = lean_ctor_get(v___x_2689_, 3);
v_traceState_2694_ = lean_ctor_get(v___x_2689_, 4);
v_recordedDeps_2695_ = lean_ctor_get(v___x_2689_, 6);
v_messages_2696_ = lean_ctor_get(v___x_2689_, 7);
v_infoState_2697_ = lean_ctor_get(v___x_2689_, 8);
v_snapshotTasks_2698_ = lean_ctor_get(v___x_2689_, 9);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2689_, 5);
lean_dec(v_unused_2730_);
v___x_2700_ = v___x_2689_;
v_isShared_2701_ = v_isSharedCheck_2729_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_snapshotTasks_2698_);
lean_inc(v_infoState_2697_);
lean_inc(v_messages_2696_);
lean_inc(v_recordedDeps_2695_);
lean_inc(v_traceState_2694_);
lean_inc(v_auxDeclNGen_2693_);
lean_inc(v_ngen_2692_);
lean_inc(v_nextMacroScope_2691_);
lean_inc(v_env_2690_);
lean_dec(v___x_2689_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2729_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2702_ = l_Lean_docStringExt;
v___x_2703_ = l_String_removeLeadingSpaces(v_a_2685_);
v___x_2704_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_2702_, v_env_2690_, v_declName_2665_, v___x_2703_, v___x_2675_);
v___x_2705_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 5, v___x_2705_);
lean_ctor_set(v___x_2700_, 0, v___x_2704_);
v___x_2707_ = v___x_2700_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_nextMacroScope_2691_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_ngen_2692_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_auxDeclNGen_2693_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_traceState_2694_);
lean_ctor_set(v_reuseFailAlloc_2728_, 5, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2728_, 6, v_recordedDeps_2695_);
lean_ctor_set(v_reuseFailAlloc_2728_, 7, v_messages_2696_);
lean_ctor_set(v_reuseFailAlloc_2728_, 8, v_infoState_2697_);
lean_ctor_set(v_reuseFailAlloc_2728_, 9, v_snapshotTasks_2698_);
v___x_2707_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_mctx_2710_; lean_object* v_zetaDeltaFVarIds_2711_; lean_object* v_postponed_2712_; lean_object* v_diag_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2726_; 
v___x_2708_ = lean_st_ref_put(v___y_2682_, v___x_2707_);
v___x_2709_ = lean_st_ref_take(v___y_2680_);
v_mctx_2710_ = lean_ctor_get(v___x_2709_, 0);
v_zetaDeltaFVarIds_2711_ = lean_ctor_get(v___x_2709_, 2);
v_postponed_2712_ = lean_ctor_get(v___x_2709_, 3);
v_diag_2713_ = lean_ctor_get(v___x_2709_, 4);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2709_, 1);
lean_dec(v_unused_2727_);
v___x_2715_ = v___x_2709_;
v_isShared_2716_ = v_isSharedCheck_2726_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_diag_2713_);
lean_inc(v_postponed_2712_);
lean_inc(v_zetaDeltaFVarIds_2711_);
lean_inc(v_mctx_2710_);
lean_dec(v___x_2709_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2726_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2718_);
v___x_2720_ = v___x_2715_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_mctx_2710_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_zetaDeltaFVarIds_2711_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_postponed_2712_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_diag_2713_);
v___x_2720_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_st_ref_put(v___y_2680_, v___x_2720_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2717_);
v___x_2723_ = v___x_2687_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2717_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_declName_2665_);
v_a_2732_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2684_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2684_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_dec(v_docComment_2666_);
lean_dec(v_declName_2665_);
return v___x_2683_;
}
}
}
else
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_dec(v_docComment_2666_);
lean_dec(v_declName_2665_);
v___x_2749_ = lean_box(0);
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0___boxed(lean_object* v_declName_2751_, lean_object* v_docComment_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2751_, v_docComment_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf(uint8_t v_isVerso_2761_, lean_object* v_declName_2762_, lean_object* v_binders_2763_, lean_object* v_docComment_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
if (v_isVerso_2761_ == 0)
{
lean_object* v___x_2772_; 
lean_dec(v_binders_2763_);
v___x_2772_ = l_Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0(v_declName_2762_, v_docComment_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_addVersoDocString(v_declName_2762_, v_binders_2763_, v_docComment_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
lean_dec(v_docComment_2764_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringOf___boxed(lean_object* v_isVerso_2774_, lean_object* v_declName_2775_, lean_object* v_binders_2776_, lean_object* v_docComment_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_){
_start:
{
uint8_t v_isVerso_boxed_2785_; lean_object* v_res_2786_; 
v_isVerso_boxed_2785_ = lean_unbox(v_isVerso_2774_);
v_res_2786_ = l_Lean_addDocStringOf(v_isVerso_boxed_2785_, v_declName_2775_, v_binders_2776_, v_docComment_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(lean_object* v_ref_2787_, lean_object* v_msgData_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___redArg(v_ref_2787_, v_msgData_2788_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_2797_, lean_object* v_msgData_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_logErrorAt___at___00Lean_validateDocComment___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__0_spec__1(v_ref_2797_, v_msgData_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v_ref_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2807_, lean_object* v_ref_2808_, lean_object* v_msg_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___redArg(v_ref_2808_, v_msg_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2818_, lean_object* v_ref_2819_, lean_object* v_msg_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00Lean_addMarkdownDocString___at___00Lean_addDocStringOf_spec__0_spec__1_spec__4(v_00_u03b1_2818_, v_ref_2819_, v_msg_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v_ref_2819_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(lean_object* v_k_2829_, lean_object* v_t_2830_){
_start:
{
if (lean_obj_tag(v_t_2830_) == 0)
{
lean_object* v_k_2831_; lean_object* v_v_2832_; lean_object* v_l_2833_; lean_object* v_r_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_3488_; 
v_k_2831_ = lean_ctor_get(v_t_2830_, 1);
v_v_2832_ = lean_ctor_get(v_t_2830_, 2);
v_l_2833_ = lean_ctor_get(v_t_2830_, 3);
v_r_2834_ = lean_ctor_get(v_t_2830_, 4);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_t_2830_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v_t_2830_, 0);
lean_dec(v_unused_3489_);
v___x_2836_ = v_t_2830_;
v_isShared_2837_ = v_isSharedCheck_3488_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_r_2834_);
lean_inc(v_l_2833_);
lean_inc(v_v_2832_);
lean_inc(v_k_2831_);
lean_dec(v_t_2830_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_3488_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint8_t v___x_2838_; 
v___x_2838_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2829_, v_k_2831_);
switch(v___x_2838_)
{
case 0:
{
lean_object* v_impl_2839_; lean_object* v___x_2840_; 
v_impl_2839_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2829_, v_l_2833_);
v___x_2840_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2839_) == 0)
{
if (lean_obj_tag(v_r_2834_) == 0)
{
lean_object* v_size_2841_; lean_object* v_size_2842_; lean_object* v_k_2843_; lean_object* v_v_2844_; lean_object* v_l_2845_; lean_object* v_r_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; 
v_size_2841_ = lean_ctor_get(v_impl_2839_, 0);
v_size_2842_ = lean_ctor_get(v_r_2834_, 0);
v_k_2843_ = lean_ctor_get(v_r_2834_, 1);
v_v_2844_ = lean_ctor_get(v_r_2834_, 2);
v_l_2845_ = lean_ctor_get(v_r_2834_, 3);
lean_inc(v_l_2845_);
v_r_2846_ = lean_ctor_get(v_r_2834_, 4);
v___x_2847_ = lean_unsigned_to_nat(3u);
v___x_2848_ = lean_nat_mul(v___x_2847_, v_size_2841_);
v___x_2849_ = lean_nat_dec_lt(v___x_2848_, v_size_2842_);
lean_dec(v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_dec(v_l_2845_);
v___x_2850_ = lean_nat_add(v___x_2840_, v_size_2841_);
v___x_2851_ = lean_nat_add(v___x_2850_, v_size_2842_);
lean_dec(v___x_2850_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 3, v_impl_2839_);
lean_ctor_set(v___x_2836_, 0, v___x_2851_);
v___x_2853_ = v___x_2836_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_impl_2839_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_r_2834_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2918_; 
lean_inc(v_r_2846_);
lean_inc(v_v_2844_);
lean_inc(v_k_2843_);
lean_inc(v_size_2842_);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; lean_object* v_unused_2920_; lean_object* v_unused_2921_; lean_object* v_unused_2922_; lean_object* v_unused_2923_; 
v_unused_2919_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_2919_);
v_unused_2920_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_r_2834_, 2);
lean_dec(v_unused_2921_);
v_unused_2922_ = lean_ctor_get(v_r_2834_, 1);
lean_dec(v_unused_2922_);
v_unused_2923_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_2923_);
v___x_2856_ = v_r_2834_;
v_isShared_2857_ = v_isSharedCheck_2918_;
goto v_resetjp_2855_;
}
else
{
lean_dec(v_r_2834_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2918_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v_size_2858_; lean_object* v_k_2859_; lean_object* v_v_2860_; lean_object* v_l_2861_; lean_object* v_r_2862_; lean_object* v_size_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; 
v_size_2858_ = lean_ctor_get(v_l_2845_, 0);
v_k_2859_ = lean_ctor_get(v_l_2845_, 1);
v_v_2860_ = lean_ctor_get(v_l_2845_, 2);
v_l_2861_ = lean_ctor_get(v_l_2845_, 3);
v_r_2862_ = lean_ctor_get(v_l_2845_, 4);
v_size_2863_ = lean_ctor_get(v_r_2846_, 0);
v___x_2864_ = lean_unsigned_to_nat(2u);
v___x_2865_ = lean_nat_mul(v___x_2864_, v_size_2863_);
v___x_2866_ = lean_nat_dec_lt(v_size_2858_, v___x_2865_);
lean_dec(v___x_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2894_; 
lean_inc(v_r_2862_);
lean_inc(v_l_2861_);
lean_inc(v_v_2860_);
lean_inc(v_k_2859_);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_l_2845_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; lean_object* v_unused_2896_; lean_object* v_unused_2897_; lean_object* v_unused_2898_; lean_object* v_unused_2899_; 
v_unused_2895_ = lean_ctor_get(v_l_2845_, 4);
lean_dec(v_unused_2895_);
v_unused_2896_ = lean_ctor_get(v_l_2845_, 3);
lean_dec(v_unused_2896_);
v_unused_2897_ = lean_ctor_get(v_l_2845_, 2);
lean_dec(v_unused_2897_);
v_unused_2898_ = lean_ctor_get(v_l_2845_, 1);
lean_dec(v_unused_2898_);
v_unused_2899_ = lean_ctor_get(v_l_2845_, 0);
lean_dec(v_unused_2899_);
v___x_2868_ = v_l_2845_;
v_isShared_2869_ = v_isSharedCheck_2894_;
goto v_resetjp_2867_;
}
else
{
lean_dec(v_l_2845_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2894_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2884_; 
v___x_2870_ = lean_nat_add(v___x_2840_, v_size_2841_);
v___x_2871_ = lean_nat_add(v___x_2870_, v_size_2842_);
lean_dec(v_size_2842_);
if (lean_obj_tag(v_l_2861_) == 0)
{
lean_object* v_size_2892_; 
v_size_2892_ = lean_ctor_get(v_l_2861_, 0);
lean_inc(v_size_2892_);
v___y_2884_ = v_size_2892_;
goto v___jp_2883_;
}
else
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v___y_2884_ = v___x_2893_;
goto v___jp_2883_;
}
v___jp_2872_:
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = lean_nat_add(v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec(v___y_2874_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 4, v_r_2846_);
lean_ctor_set(v___x_2868_, 3, v_r_2862_);
lean_ctor_set(v___x_2868_, 2, v_v_2844_);
lean_ctor_set(v___x_2868_, 1, v_k_2843_);
lean_ctor_set(v___x_2868_, 0, v___x_2876_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_k_2843_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_v_2844_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_r_2862_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_r_2846_);
v___x_2878_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 4, v___x_2878_);
lean_ctor_set(v___x_2856_, 3, v___y_2873_);
lean_ctor_set(v___x_2856_, 2, v_v_2860_);
lean_ctor_set(v___x_2856_, 1, v_k_2859_);
lean_ctor_set(v___x_2856_, 0, v___x_2871_);
v___x_2880_ = v___x_2856_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_k_2859_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_v_2860_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v___y_2873_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
v___jp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2885_ = lean_nat_add(v___x_2870_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec(v___x_2870_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_l_2861_);
lean_ctor_set(v___x_2836_, 3, v_impl_2839_);
lean_ctor_set(v___x_2836_, 0, v___x_2885_);
v___x_2887_ = v___x_2836_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2891_, 3, v_impl_2839_);
lean_ctor_set(v_reuseFailAlloc_2891_, 4, v_l_2861_);
v___x_2887_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_nat_add(v___x_2840_, v_size_2863_);
if (lean_obj_tag(v_r_2862_) == 0)
{
lean_object* v_size_2889_; 
v_size_2889_ = lean_ctor_get(v_r_2862_, 0);
lean_inc(v_size_2889_);
v___y_2873_ = v___x_2887_;
v___y_2874_ = v___x_2888_;
v___y_2875_ = v_size_2889_;
goto v___jp_2872_;
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_unsigned_to_nat(0u);
v___y_2873_ = v___x_2887_;
v___y_2874_ = v___x_2888_;
v___y_2875_ = v___x_2890_;
goto v___jp_2872_;
}
}
}
}
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_del_object(v___x_2836_);
v___x_2900_ = lean_nat_add(v___x_2840_, v_size_2841_);
v___x_2901_ = lean_nat_add(v___x_2900_, v_size_2842_);
lean_dec(v_size_2842_);
v___x_2902_ = lean_nat_add(v___x_2900_, v_size_2858_);
lean_dec(v___x_2900_);
lean_inc_ref(v_impl_2839_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 4, v_l_2845_);
lean_ctor_set(v___x_2856_, 3, v_impl_2839_);
lean_ctor_set(v___x_2856_, 2, v_v_2832_);
lean_ctor_set(v___x_2856_, 1, v_k_2831_);
lean_ctor_set(v___x_2856_, 0, v___x_2902_);
v___x_2904_ = v___x_2856_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2917_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2917_, 3, v_impl_2839_);
lean_ctor_set(v_reuseFailAlloc_2917_, 4, v_l_2845_);
v___x_2904_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_isSharedCheck_2911_ = !lean_is_exclusive(v_impl_2839_);
if (v_isSharedCheck_2911_ == 0)
{
lean_object* v_unused_2912_; lean_object* v_unused_2913_; lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; 
v_unused_2912_ = lean_ctor_get(v_impl_2839_, 4);
lean_dec(v_unused_2912_);
v_unused_2913_ = lean_ctor_get(v_impl_2839_, 3);
lean_dec(v_unused_2913_);
v_unused_2914_ = lean_ctor_get(v_impl_2839_, 2);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_impl_2839_, 1);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_impl_2839_, 0);
lean_dec(v_unused_2916_);
v___x_2906_ = v_impl_2839_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_dec(v_impl_2839_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 4, v_r_2846_);
lean_ctor_set(v___x_2906_, 3, v___x_2904_);
lean_ctor_set(v___x_2906_, 2, v_v_2844_);
lean_ctor_set(v___x_2906_, 1, v_k_2843_);
lean_ctor_set(v___x_2906_, 0, v___x_2901_);
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_k_2843_);
lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_v_2844_);
lean_ctor_set(v_reuseFailAlloc_2910_, 3, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_r_2846_);
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
}
}
}
else
{
lean_object* v_size_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v_size_2924_ = lean_ctor_get(v_impl_2839_, 0);
v___x_2925_ = lean_nat_add(v___x_2840_, v_size_2924_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 3, v_impl_2839_);
lean_ctor_set(v___x_2836_, 0, v___x_2925_);
v___x_2927_ = v___x_2836_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_impl_2839_);
lean_ctor_set(v_reuseFailAlloc_2928_, 4, v_r_2834_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
if (lean_obj_tag(v_r_2834_) == 0)
{
lean_object* v_l_2929_; 
v_l_2929_ = lean_ctor_get(v_r_2834_, 3);
lean_inc(v_l_2929_);
if (lean_obj_tag(v_l_2929_) == 0)
{
lean_object* v_r_2930_; 
v_r_2930_ = lean_ctor_get(v_r_2834_, 4);
lean_inc(v_r_2930_);
if (lean_obj_tag(v_r_2930_) == 0)
{
lean_object* v_size_2931_; lean_object* v_k_2932_; lean_object* v_v_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2946_; 
v_size_2931_ = lean_ctor_get(v_r_2834_, 0);
v_k_2932_ = lean_ctor_get(v_r_2834_, 1);
v_v_2933_ = lean_ctor_get(v_r_2834_, 2);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_2946_ == 0)
{
lean_object* v_unused_2947_; lean_object* v_unused_2948_; 
v_unused_2947_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_2948_);
v___x_2935_ = v_r_2834_;
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_v_2933_);
lean_inc(v_k_2932_);
lean_inc(v_size_2931_);
lean_dec(v_r_2834_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2946_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v_size_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v_size_2937_ = lean_ctor_get(v_l_2929_, 0);
v___x_2938_ = lean_nat_add(v___x_2840_, v_size_2931_);
lean_dec(v_size_2931_);
v___x_2939_ = lean_nat_add(v___x_2840_, v_size_2937_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 4, v_l_2929_);
lean_ctor_set(v___x_2935_, 3, v_impl_2839_);
lean_ctor_set(v___x_2935_, 2, v_v_2832_);
lean_ctor_set(v___x_2935_, 1, v_k_2831_);
lean_ctor_set(v___x_2935_, 0, v___x_2939_);
v___x_2941_ = v___x_2935_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_impl_2839_);
lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_l_2929_);
v___x_2941_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2943_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_r_2930_);
lean_ctor_set(v___x_2836_, 3, v___x_2941_);
lean_ctor_set(v___x_2836_, 2, v_v_2933_);
lean_ctor_set(v___x_2836_, 1, v_k_2932_);
lean_ctor_set(v___x_2836_, 0, v___x_2938_);
v___x_2943_ = v___x_2836_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_k_2932_);
lean_ctor_set(v_reuseFailAlloc_2944_, 2, v_v_2933_);
lean_ctor_set(v_reuseFailAlloc_2944_, 3, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2944_, 4, v_r_2930_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_k_2949_; lean_object* v_v_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2973_; 
v_k_2949_ = lean_ctor_get(v_r_2834_, 1);
v_v_2950_ = lean_ctor_get(v_r_2834_, 2);
v_isSharedCheck_2973_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; lean_object* v_unused_2975_; lean_object* v_unused_2976_; 
v_unused_2974_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_2975_);
v_unused_2976_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_2976_);
v___x_2952_ = v_r_2834_;
v_isShared_2953_ = v_isSharedCheck_2973_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_v_2950_);
lean_inc(v_k_2949_);
lean_dec(v_r_2834_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2973_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_k_2954_; lean_object* v_v_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2969_; 
v_k_2954_ = lean_ctor_get(v_l_2929_, 1);
v_v_2955_ = lean_ctor_get(v_l_2929_, 2);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_l_2929_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; lean_object* v_unused_2971_; lean_object* v_unused_2972_; 
v_unused_2970_ = lean_ctor_get(v_l_2929_, 4);
lean_dec(v_unused_2970_);
v_unused_2971_ = lean_ctor_get(v_l_2929_, 3);
lean_dec(v_unused_2971_);
v_unused_2972_ = lean_ctor_get(v_l_2929_, 0);
lean_dec(v_unused_2972_);
v___x_2957_ = v_l_2929_;
v_isShared_2958_ = v_isSharedCheck_2969_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_v_2955_);
lean_inc(v_k_2954_);
lean_dec(v_l_2929_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2969_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2959_ = lean_unsigned_to_nat(3u);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 4, v_r_2930_);
lean_ctor_set(v___x_2957_, 3, v_r_2930_);
lean_ctor_set(v___x_2957_, 2, v_v_2832_);
lean_ctor_set(v___x_2957_, 1, v_k_2831_);
lean_ctor_set(v___x_2957_, 0, v___x_2840_);
v___x_2961_ = v___x_2957_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2968_, 3, v_r_2930_);
lean_ctor_set(v_reuseFailAlloc_2968_, 4, v_r_2930_);
v___x_2961_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2963_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 3, v_r_2930_);
lean_ctor_set(v___x_2952_, 0, v___x_2840_);
v___x_2963_ = v___x_2952_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v_k_2949_);
lean_ctor_set(v_reuseFailAlloc_2967_, 2, v_v_2950_);
lean_ctor_set(v_reuseFailAlloc_2967_, 3, v_r_2930_);
lean_ctor_set(v_reuseFailAlloc_2967_, 4, v_r_2930_);
v___x_2963_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2965_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_2963_);
lean_ctor_set(v___x_2836_, 3, v___x_2961_);
lean_ctor_set(v___x_2836_, 2, v_v_2955_);
lean_ctor_set(v___x_2836_, 1, v_k_2954_);
lean_ctor_set(v___x_2836_, 0, v___x_2959_);
v___x_2965_ = v___x_2836_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_k_2954_);
lean_ctor_set(v_reuseFailAlloc_2966_, 2, v_v_2955_);
lean_ctor_set(v_reuseFailAlloc_2966_, 3, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2966_, 4, v___x_2963_);
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
lean_object* v_r_2977_; 
v_r_2977_ = lean_ctor_get(v_r_2834_, 4);
lean_inc(v_r_2977_);
if (lean_obj_tag(v_r_2977_) == 0)
{
lean_object* v_k_2978_; lean_object* v_v_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2990_; 
v_k_2978_ = lean_ctor_get(v_r_2834_, 1);
v_v_2979_ = lean_ctor_get(v_r_2834_, 2);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; lean_object* v_unused_2992_; lean_object* v_unused_2993_; 
v_unused_2991_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_2991_);
v_unused_2992_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_2992_);
v_unused_2993_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_2993_);
v___x_2981_ = v_r_2834_;
v_isShared_2982_ = v_isSharedCheck_2990_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_v_2979_);
lean_inc(v_k_2978_);
lean_dec(v_r_2834_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2990_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(3u);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 4, v_l_2929_);
lean_ctor_set(v___x_2981_, 2, v_v_2832_);
lean_ctor_set(v___x_2981_, 1, v_k_2831_);
lean_ctor_set(v___x_2981_, 0, v___x_2840_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_2989_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_2989_, 3, v_l_2929_);
lean_ctor_set(v_reuseFailAlloc_2989_, 4, v_l_2929_);
v___x_2985_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2987_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_r_2977_);
lean_ctor_set(v___x_2836_, 3, v___x_2985_);
lean_ctor_set(v___x_2836_, 2, v_v_2979_);
lean_ctor_set(v___x_2836_, 1, v_k_2978_);
lean_ctor_set(v___x_2836_, 0, v___x_2983_);
v___x_2987_ = v___x_2836_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_k_2978_);
lean_ctor_set(v_reuseFailAlloc_2988_, 2, v_v_2979_);
lean_ctor_set(v_reuseFailAlloc_2988_, 3, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_2988_, 4, v_r_2977_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_size_2994_; lean_object* v_k_2995_; lean_object* v_v_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3007_; 
v_size_2994_ = lean_ctor_get(v_r_2834_, 0);
v_k_2995_ = lean_ctor_get(v_r_2834_, 1);
v_v_2996_ = lean_ctor_get(v_r_2834_, 2);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; lean_object* v_unused_3009_; 
v_unused_3008_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_3008_);
v_unused_3009_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_3009_);
v___x_2998_ = v_r_2834_;
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_v_2996_);
lean_inc(v_k_2995_);
lean_inc(v_size_2994_);
lean_dec(v_r_2834_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 3, v_r_2977_);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_size_2994_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_k_2995_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_v_2996_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_r_2977_);
lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_r_2977_);
v___x_3001_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = lean_unsigned_to_nat(2u);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_3001_);
lean_ctor_set(v___x_2836_, 3, v_r_2977_);
lean_ctor_set(v___x_2836_, 0, v___x_3002_);
v___x_3004_ = v___x_2836_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_r_2977_);
lean_ctor_set(v_reuseFailAlloc_3005_, 4, v___x_3001_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
else
{
lean_object* v___x_3011_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 3, v_r_2834_);
lean_ctor_set(v___x_2836_, 0, v___x_2840_);
v___x_3011_ = v___x_2836_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_r_2834_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_r_2834_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
case 1:
{
lean_del_object(v___x_2836_);
lean_dec(v_v_2832_);
lean_dec(v_k_2831_);
if (lean_obj_tag(v_l_2833_) == 0)
{
if (lean_obj_tag(v_r_2834_) == 0)
{
lean_object* v_size_3013_; lean_object* v_k_3014_; lean_object* v_v_3015_; lean_object* v_l_3016_; lean_object* v_r_3017_; lean_object* v_size_3018_; lean_object* v_k_3019_; lean_object* v_v_3020_; lean_object* v_l_3021_; lean_object* v_r_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; 
v_size_3013_ = lean_ctor_get(v_l_2833_, 0);
v_k_3014_ = lean_ctor_get(v_l_2833_, 1);
v_v_3015_ = lean_ctor_get(v_l_2833_, 2);
v_l_3016_ = lean_ctor_get(v_l_2833_, 3);
v_r_3017_ = lean_ctor_get(v_l_2833_, 4);
lean_inc(v_r_3017_);
v_size_3018_ = lean_ctor_get(v_r_2834_, 0);
v_k_3019_ = lean_ctor_get(v_r_2834_, 1);
v_v_3020_ = lean_ctor_get(v_r_2834_, 2);
v_l_3021_ = lean_ctor_get(v_r_2834_, 3);
lean_inc(v_l_3021_);
v_r_3022_ = lean_ctor_get(v_r_2834_, 4);
v___x_3023_ = lean_unsigned_to_nat(1u);
v___x_3024_ = lean_nat_dec_lt(v_size_3013_, v_size_3018_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_l_3016_);
lean_inc(v_v_3015_);
lean_inc(v_k_3014_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3161_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_l_2833_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_l_2833_, 1);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3165_);
v___x_3026_ = v_l_2833_;
v_isShared_3027_ = v_isSharedCheck_3160_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v_l_2833_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3160_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v_tree_3029_; 
v___x_3028_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_3014_, v_v_3015_, v_l_3016_, v_r_3017_);
v_tree_3029_ = lean_ctor_get(v___x_3028_, 2);
if (lean_obj_tag(v_tree_3029_) == 0)
{
lean_object* v_k_3030_; lean_object* v_v_3031_; lean_object* v_size_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
lean_inc_ref(v_tree_3029_);
v_k_3030_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_k_3030_);
v_v_3031_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_v_3031_);
lean_dec_ref(v___x_3028_);
v_size_3032_ = lean_ctor_get(v_tree_3029_, 0);
v___x_3033_ = lean_unsigned_to_nat(3u);
v___x_3034_ = lean_nat_mul(v___x_3033_, v_size_3032_);
v___x_3035_ = lean_nat_dec_lt(v___x_3034_, v_size_3018_);
lean_dec(v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
lean_dec(v_l_3021_);
v___x_3036_ = lean_nat_add(v___x_3023_, v_size_3032_);
v___x_3037_ = lean_nat_add(v___x_3036_, v_size_3018_);
lean_dec(v___x_3036_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v_r_2834_);
lean_ctor_set(v___x_3026_, 3, v_tree_3029_);
lean_ctor_set(v___x_3026_, 2, v_v_3031_);
lean_ctor_set(v___x_3026_, 1, v_k_3030_);
lean_ctor_set(v___x_3026_, 0, v___x_3037_);
v___x_3039_ = v___x_3026_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v_k_3030_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v_v_3031_);
lean_ctor_set(v_reuseFailAlloc_3040_, 3, v_tree_3029_);
lean_ctor_set(v_reuseFailAlloc_3040_, 4, v_r_2834_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
else
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3095_; 
lean_inc(v_r_3022_);
lean_inc(v_v_3020_);
lean_inc(v_k_3019_);
lean_inc(v_size_3018_);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; lean_object* v_unused_3097_; lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3096_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_3097_);
v_unused_3098_ = lean_ctor_get(v_r_2834_, 2);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_r_2834_, 1);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_3100_);
v___x_3042_ = v_r_2834_;
v_isShared_3043_ = v_isSharedCheck_3095_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v_r_2834_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3095_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_size_3044_; lean_object* v_k_3045_; lean_object* v_v_3046_; lean_object* v_l_3047_; lean_object* v_r_3048_; lean_object* v_size_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_size_3044_ = lean_ctor_get(v_l_3021_, 0);
v_k_3045_ = lean_ctor_get(v_l_3021_, 1);
v_v_3046_ = lean_ctor_get(v_l_3021_, 2);
v_l_3047_ = lean_ctor_get(v_l_3021_, 3);
v_r_3048_ = lean_ctor_get(v_l_3021_, 4);
v_size_3049_ = lean_ctor_get(v_r_3022_, 0);
v___x_3050_ = lean_unsigned_to_nat(2u);
v___x_3051_ = lean_nat_mul(v___x_3050_, v_size_3049_);
v___x_3052_ = lean_nat_dec_lt(v_size_3044_, v___x_3051_);
lean_dec(v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3080_; 
lean_inc(v_r_3048_);
lean_inc(v_l_3047_);
lean_inc(v_v_3046_);
lean_inc(v_k_3045_);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_l_3021_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; lean_object* v_unused_3082_; lean_object* v_unused_3083_; lean_object* v_unused_3084_; lean_object* v_unused_3085_; 
v_unused_3081_ = lean_ctor_get(v_l_3021_, 4);
lean_dec(v_unused_3081_);
v_unused_3082_ = lean_ctor_get(v_l_3021_, 3);
lean_dec(v_unused_3082_);
v_unused_3083_ = lean_ctor_get(v_l_3021_, 2);
lean_dec(v_unused_3083_);
v_unused_3084_ = lean_ctor_get(v_l_3021_, 1);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_l_3021_, 0);
lean_dec(v_unused_3085_);
v___x_3054_ = v_l_3021_;
v_isShared_3055_ = v_isSharedCheck_3080_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v_l_3021_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3080_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3070_; 
v___x_3056_ = lean_nat_add(v___x_3023_, v_size_3032_);
v___x_3057_ = lean_nat_add(v___x_3056_, v_size_3018_);
lean_dec(v_size_3018_);
if (lean_obj_tag(v_l_3047_) == 0)
{
lean_object* v_size_3078_; 
v_size_3078_ = lean_ctor_get(v_l_3047_, 0);
lean_inc(v_size_3078_);
v___y_3070_ = v_size_3078_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___y_3070_ = v___x_3079_;
goto v___jp_3069_;
}
v___jp_3058_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = lean_nat_add(v___y_3059_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec(v___y_3059_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 4, v_r_3022_);
lean_ctor_set(v___x_3054_, 3, v_r_3048_);
lean_ctor_set(v___x_3054_, 2, v_v_3020_);
lean_ctor_set(v___x_3054_, 1, v_k_3019_);
lean_ctor_set(v___x_3054_, 0, v___x_3062_);
v___x_3064_ = v___x_3054_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_r_3048_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_r_3022_);
v___x_3064_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v___x_3064_);
lean_ctor_set(v___x_3042_, 3, v___y_3060_);
lean_ctor_set(v___x_3042_, 2, v_v_3046_);
lean_ctor_set(v___x_3042_, 1, v_k_3045_);
lean_ctor_set(v___x_3042_, 0, v___x_3057_);
v___x_3066_ = v___x_3042_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_k_3045_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_v_3046_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v___y_3060_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
v___jp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_nat_add(v___x_3056_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec(v___x_3056_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v_l_3047_);
lean_ctor_set(v___x_3026_, 3, v_tree_3029_);
lean_ctor_set(v___x_3026_, 2, v_v_3031_);
lean_ctor_set(v___x_3026_, 1, v_k_3030_);
lean_ctor_set(v___x_3026_, 0, v___x_3071_);
v___x_3073_ = v___x_3026_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_k_3030_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_v_3031_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_tree_3029_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_l_3047_);
v___x_3073_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_nat_add(v___x_3023_, v_size_3049_);
if (lean_obj_tag(v_r_3048_) == 0)
{
lean_object* v_size_3075_; 
v_size_3075_ = lean_ctor_get(v_r_3048_, 0);
lean_inc(v_size_3075_);
v___y_3059_ = v___x_3074_;
v___y_3060_ = v___x_3073_;
v___y_3061_ = v_size_3075_;
goto v___jp_3058_;
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_unsigned_to_nat(0u);
v___y_3059_ = v___x_3074_;
v___y_3060_ = v___x_3073_;
v___y_3061_ = v___x_3076_;
goto v___jp_3058_;
}
}
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3086_ = lean_nat_add(v___x_3023_, v_size_3032_);
v___x_3087_ = lean_nat_add(v___x_3086_, v_size_3018_);
lean_dec(v_size_3018_);
v___x_3088_ = lean_nat_add(v___x_3086_, v_size_3044_);
lean_dec(v___x_3086_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 4, v_l_3021_);
lean_ctor_set(v___x_3042_, 3, v_tree_3029_);
lean_ctor_set(v___x_3042_, 2, v_v_3031_);
lean_ctor_set(v___x_3042_, 1, v_k_3030_);
lean_ctor_set(v___x_3042_, 0, v___x_3088_);
v___x_3090_ = v___x_3042_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3088_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_k_3030_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_v_3031_);
lean_ctor_set(v_reuseFailAlloc_3094_, 3, v_tree_3029_);
lean_ctor_set(v_reuseFailAlloc_3094_, 4, v_l_3021_);
v___x_3090_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v_r_3022_);
lean_ctor_set(v___x_3026_, 3, v___x_3090_);
lean_ctor_set(v___x_3026_, 2, v_v_3020_);
lean_ctor_set(v___x_3026_, 1, v_k_3019_);
lean_ctor_set(v___x_3026_, 0, v___x_3087_);
v___x_3092_ = v___x_3026_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3093_, 3, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3093_, 4, v_r_3022_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
else
{
lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3154_; 
lean_inc(v_r_3022_);
lean_inc(v_v_3020_);
lean_inc(v_k_3019_);
lean_inc(v_size_3018_);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; lean_object* v_unused_3156_; lean_object* v_unused_3157_; lean_object* v_unused_3158_; lean_object* v_unused_3159_; 
v_unused_3155_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_r_2834_, 2);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_r_2834_, 1);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_3159_);
v___x_3102_ = v_r_2834_;
v_isShared_3103_ = v_isSharedCheck_3154_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v_r_2834_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3154_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
if (lean_obj_tag(v_l_3021_) == 0)
{
if (lean_obj_tag(v_r_3022_) == 0)
{
lean_object* v_k_3104_; lean_object* v_v_3105_; lean_object* v_size_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_inc(v_tree_3029_);
v_k_3104_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_k_3104_);
v_v_3105_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_v_3105_);
lean_dec_ref(v___x_3028_);
v_size_3106_ = lean_ctor_get(v_l_3021_, 0);
v___x_3107_ = lean_nat_add(v___x_3023_, v_size_3018_);
lean_dec(v_size_3018_);
v___x_3108_ = lean_nat_add(v___x_3023_, v_size_3106_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 4, v_l_3021_);
lean_ctor_set(v___x_3102_, 3, v_tree_3029_);
lean_ctor_set(v___x_3102_, 2, v_v_3105_);
lean_ctor_set(v___x_3102_, 1, v_k_3104_);
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3104_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3105_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_tree_3029_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_l_3021_);
v___x_3110_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3112_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v_r_3022_);
lean_ctor_set(v___x_3026_, 3, v___x_3110_);
lean_ctor_set(v___x_3026_, 2, v_v_3020_);
lean_ctor_set(v___x_3026_, 1, v_k_3019_);
lean_ctor_set(v___x_3026_, 0, v___x_3107_);
v___x_3112_ = v___x_3026_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3113_, 3, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3113_, 4, v_r_3022_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
else
{
lean_object* v_k_3115_; lean_object* v_v_3116_; lean_object* v_k_3117_; lean_object* v_v_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3132_; 
lean_dec(v_size_3018_);
v_k_3115_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_k_3115_);
v_v_3116_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_v_3116_);
lean_dec_ref(v___x_3028_);
v_k_3117_ = lean_ctor_get(v_l_3021_, 1);
v_v_3118_ = lean_ctor_get(v_l_3021_, 2);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_l_3021_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; 
v_unused_3133_ = lean_ctor_get(v_l_3021_, 4);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_l_3021_, 3);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_l_3021_, 0);
lean_dec(v_unused_3135_);
v___x_3120_ = v_l_3021_;
v_isShared_3121_ = v_isSharedCheck_3132_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_v_3118_);
lean_inc(v_k_3117_);
lean_dec(v_l_3021_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3132_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_unsigned_to_nat(3u);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 4, v_r_3022_);
lean_ctor_set(v___x_3120_, 3, v_r_3022_);
lean_ctor_set(v___x_3120_, 2, v_v_3116_);
lean_ctor_set(v___x_3120_, 1, v_k_3115_);
lean_ctor_set(v___x_3120_, 0, v___x_3023_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3115_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3116_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_r_3022_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_r_3022_);
v___x_3124_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3126_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 3, v_r_3022_);
lean_ctor_set(v___x_3102_, 0, v___x_3023_);
v___x_3126_ = v___x_3102_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_r_3022_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_r_3022_);
v___x_3126_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v___x_3126_);
lean_ctor_set(v___x_3026_, 3, v___x_3124_);
lean_ctor_set(v___x_3026_, 2, v_v_3118_);
lean_ctor_set(v___x_3026_, 1, v_k_3117_);
lean_ctor_set(v___x_3026_, 0, v___x_3122_);
v___x_3128_ = v___x_3026_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_k_3117_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_v_3118_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3022_) == 0)
{
lean_object* v_k_3136_; lean_object* v_v_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
lean_dec(v_size_3018_);
v_k_3136_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_k_3136_);
v_v_3137_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_v_3137_);
lean_dec_ref(v___x_3028_);
v___x_3138_ = lean_unsigned_to_nat(3u);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 4, v_l_3021_);
lean_ctor_set(v___x_3102_, 2, v_v_3137_);
lean_ctor_set(v___x_3102_, 1, v_k_3136_);
lean_ctor_set(v___x_3102_, 0, v___x_3023_);
v___x_3140_ = v___x_3102_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_k_3136_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_v_3137_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_l_3021_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_l_3021_);
v___x_3140_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3142_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v_r_3022_);
lean_ctor_set(v___x_3026_, 3, v___x_3140_);
lean_ctor_set(v___x_3026_, 2, v_v_3020_);
lean_ctor_set(v___x_3026_, 1, v_k_3019_);
lean_ctor_set(v___x_3026_, 0, v___x_3138_);
v___x_3142_ = v___x_3026_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_r_3022_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_object* v_k_3145_; lean_object* v_v_3146_; lean_object* v___x_3148_; 
v_k_3145_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_k_3145_);
v_v_3146_ = lean_ctor_get(v___x_3028_, 1);
lean_inc(v_v_3146_);
lean_dec_ref(v___x_3028_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 3, v_r_3022_);
v___x_3148_ = v___x_3102_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_size_3018_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_k_3019_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_v_3020_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_r_3022_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v_r_3022_);
v___x_3148_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_unsigned_to_nat(2u);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 4, v___x_3148_);
lean_ctor_set(v___x_3026_, 3, v_r_3022_);
lean_ctor_set(v___x_3026_, 2, v_v_3146_);
lean_ctor_set(v___x_3026_, 1, v_k_3145_);
lean_ctor_set(v___x_3026_, 0, v___x_3149_);
v___x_3151_ = v___x_3026_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_k_3145_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v_v_3146_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v_r_3022_);
lean_ctor_set(v_reuseFailAlloc_3152_, 4, v___x_3148_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
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
lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3318_; 
lean_inc(v_r_3022_);
lean_inc(v_v_3020_);
lean_inc(v_k_3019_);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_r_2834_);
if (v_isSharedCheck_3318_ == 0)
{
lean_object* v_unused_3319_; lean_object* v_unused_3320_; lean_object* v_unused_3321_; lean_object* v_unused_3322_; lean_object* v_unused_3323_; 
v_unused_3319_ = lean_ctor_get(v_r_2834_, 4);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_r_2834_, 3);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_r_2834_, 2);
lean_dec(v_unused_3321_);
v_unused_3322_ = lean_ctor_get(v_r_2834_, 1);
lean_dec(v_unused_3322_);
v_unused_3323_ = lean_ctor_get(v_r_2834_, 0);
lean_dec(v_unused_3323_);
v___x_3167_ = v_r_2834_;
v_isShared_3168_ = v_isSharedCheck_3318_;
goto v_resetjp_3166_;
}
else
{
lean_dec(v_r_2834_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3318_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v_tree_3170_; 
v___x_3169_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_3019_, v_v_3020_, v_l_3021_, v_r_3022_);
v_tree_3170_ = lean_ctor_get(v___x_3169_, 2);
lean_inc(v_tree_3170_);
if (lean_obj_tag(v_tree_3170_) == 0)
{
lean_object* v_k_3171_; lean_object* v_v_3172_; lean_object* v_size_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_k_3171_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_k_3171_);
v_v_3172_ = lean_ctor_get(v___x_3169_, 1);
lean_inc(v_v_3172_);
lean_dec_ref(v___x_3169_);
v_size_3173_ = lean_ctor_get(v_tree_3170_, 0);
v___x_3174_ = lean_unsigned_to_nat(3u);
v___x_3175_ = lean_nat_mul(v___x_3174_, v_size_3173_);
v___x_3176_ = lean_nat_dec_lt(v___x_3175_, v_size_3013_);
lean_dec(v___x_3175_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_dec(v_r_3017_);
v___x_3177_ = lean_nat_add(v___x_3023_, v_size_3013_);
v___x_3178_ = lean_nat_add(v___x_3177_, v_size_3173_);
lean_dec(v___x_3177_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_tree_3170_);
lean_ctor_set(v___x_3167_, 3, v_l_2833_);
lean_ctor_set(v___x_3167_, 2, v_v_3172_);
lean_ctor_set(v___x_3167_, 1, v_k_3171_);
lean_ctor_set(v___x_3167_, 0, v___x_3178_);
v___x_3180_ = v___x_3167_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_k_3171_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_v_3172_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_tree_3170_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
else
{
lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3247_; 
lean_inc(v_l_3016_);
lean_inc(v_v_3015_);
lean_inc(v_k_3014_);
lean_inc(v_size_3013_);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; lean_object* v_unused_3250_; lean_object* v_unused_3251_; lean_object* v_unused_3252_; 
v_unused_3248_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_l_2833_, 2);
lean_dec(v_unused_3250_);
v_unused_3251_ = lean_ctor_get(v_l_2833_, 1);
lean_dec(v_unused_3251_);
v_unused_3252_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3252_);
v___x_3183_ = v_l_2833_;
v_isShared_3184_ = v_isSharedCheck_3247_;
goto v_resetjp_3182_;
}
else
{
lean_dec(v_l_2833_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3247_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_size_3185_; lean_object* v_size_3186_; lean_object* v_k_3187_; lean_object* v_v_3188_; lean_object* v_l_3189_; lean_object* v_r_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; uint8_t v___x_3193_; 
v_size_3185_ = lean_ctor_get(v_l_3016_, 0);
v_size_3186_ = lean_ctor_get(v_r_3017_, 0);
v_k_3187_ = lean_ctor_get(v_r_3017_, 1);
v_v_3188_ = lean_ctor_get(v_r_3017_, 2);
v_l_3189_ = lean_ctor_get(v_r_3017_, 3);
v_r_3190_ = lean_ctor_get(v_r_3017_, 4);
v___x_3191_ = lean_unsigned_to_nat(2u);
v___x_3192_ = lean_nat_mul(v___x_3191_, v_size_3185_);
v___x_3193_ = lean_nat_dec_lt(v_size_3186_, v___x_3192_);
lean_dec(v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3231_; 
lean_inc(v_r_3190_);
lean_inc(v_l_3189_);
lean_inc(v_v_3188_);
lean_inc(v_k_3187_);
lean_del_object(v___x_3183_);
v_isSharedCheck_3231_ = !lean_is_exclusive(v_r_3017_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; lean_object* v_unused_3236_; 
v_unused_3232_ = lean_ctor_get(v_r_3017_, 4);
lean_dec(v_unused_3232_);
v_unused_3233_ = lean_ctor_get(v_r_3017_, 3);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_r_3017_, 2);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_r_3017_, 1);
lean_dec(v_unused_3235_);
v_unused_3236_ = lean_ctor_get(v_r_3017_, 0);
lean_dec(v_unused_3236_);
v___x_3195_ = v_r_3017_;
v_isShared_3196_ = v_isSharedCheck_3231_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v_r_3017_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3231_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___x_3219_; lean_object* v___y_3221_; 
v___x_3197_ = lean_nat_add(v___x_3023_, v_size_3013_);
lean_dec(v_size_3013_);
v___x_3198_ = lean_nat_add(v___x_3197_, v_size_3173_);
lean_dec(v___x_3197_);
v___x_3219_ = lean_nat_add(v___x_3023_, v_size_3185_);
if (lean_obj_tag(v_l_3189_) == 0)
{
lean_object* v_size_3229_; 
v_size_3229_ = lean_ctor_get(v_l_3189_, 0);
lean_inc(v_size_3229_);
v___y_3221_ = v_size_3229_;
goto v___jp_3220_;
}
else
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_unsigned_to_nat(0u);
v___y_3221_ = v___x_3230_;
goto v___jp_3220_;
}
v___jp_3199_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_nat_add(v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec(v___y_3201_);
lean_inc_ref(v_tree_3170_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 4, v_tree_3170_);
lean_ctor_set(v___x_3195_, 3, v_r_3190_);
lean_ctor_set(v___x_3195_, 2, v_v_3172_);
lean_ctor_set(v___x_3195_, 1, v_k_3171_);
lean_ctor_set(v___x_3195_, 0, v___x_3203_);
v___x_3205_ = v___x_3195_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_k_3171_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_v_3172_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_r_3190_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_tree_3170_);
v___x_3205_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
v_isSharedCheck_3212_ = !lean_is_exclusive(v_tree_3170_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; lean_object* v_unused_3214_; lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; 
v_unused_3213_ = lean_ctor_get(v_tree_3170_, 4);
lean_dec(v_unused_3213_);
v_unused_3214_ = lean_ctor_get(v_tree_3170_, 3);
lean_dec(v_unused_3214_);
v_unused_3215_ = lean_ctor_get(v_tree_3170_, 2);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_tree_3170_, 1);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_tree_3170_, 0);
lean_dec(v_unused_3217_);
v___x_3207_ = v_tree_3170_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v_tree_3170_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 4, v___x_3205_);
lean_ctor_set(v___x_3207_, 3, v___y_3200_);
lean_ctor_set(v___x_3207_, 2, v_v_3188_);
lean_ctor_set(v___x_3207_, 1, v_k_3187_);
lean_ctor_set(v___x_3207_, 0, v___x_3198_);
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_k_3187_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_v_3188_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v___y_3200_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___x_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_nat_add(v___x_3219_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec(v___x_3219_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_l_3189_);
lean_ctor_set(v___x_3167_, 3, v_l_3016_);
lean_ctor_set(v___x_3167_, 2, v_v_3015_);
lean_ctor_set(v___x_3167_, 1, v_k_3014_);
lean_ctor_set(v___x_3167_, 0, v___x_3222_);
v___x_3224_ = v___x_3167_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_l_3189_);
v___x_3224_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_nat_add(v___x_3023_, v_size_3173_);
if (lean_obj_tag(v_r_3190_) == 0)
{
lean_object* v_size_3226_; 
v_size_3226_ = lean_ctor_get(v_r_3190_, 0);
lean_inc(v_size_3226_);
v___y_3200_ = v___x_3224_;
v___y_3201_ = v___x_3225_;
v___y_3202_ = v_size_3226_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_unsigned_to_nat(0u);
v___y_3200_ = v___x_3224_;
v___y_3201_ = v___x_3225_;
v___y_3202_ = v___x_3227_;
goto v___jp_3199_;
}
}
}
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3237_ = lean_nat_add(v___x_3023_, v_size_3013_);
lean_dec(v_size_3013_);
v___x_3238_ = lean_nat_add(v___x_3237_, v_size_3173_);
lean_dec(v___x_3237_);
v___x_3239_ = lean_nat_add(v___x_3023_, v_size_3173_);
v___x_3240_ = lean_nat_add(v___x_3239_, v_size_3186_);
lean_dec(v___x_3239_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_tree_3170_);
lean_ctor_set(v___x_3167_, 3, v_r_3017_);
lean_ctor_set(v___x_3167_, 2, v_v_3172_);
lean_ctor_set(v___x_3167_, 1, v_k_3171_);
lean_ctor_set(v___x_3167_, 0, v___x_3240_);
v___x_3242_ = v___x_3167_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_k_3171_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_v_3172_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_r_3017_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_tree_3170_);
v___x_3242_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3244_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 4, v___x_3242_);
lean_ctor_set(v___x_3183_, 0, v___x_3238_);
v___x_3244_ = v___x_3183_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_3016_) == 0)
{
lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3276_; 
lean_inc_ref(v_l_3016_);
lean_inc(v_v_3015_);
lean_inc(v_k_3014_);
lean_inc(v_size_3013_);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; lean_object* v_unused_3278_; lean_object* v_unused_3279_; lean_object* v_unused_3280_; lean_object* v_unused_3281_; 
v_unused_3277_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3277_);
v_unused_3278_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3278_);
v_unused_3279_ = lean_ctor_get(v_l_2833_, 2);
lean_dec(v_unused_3279_);
v_unused_3280_ = lean_ctor_get(v_l_2833_, 1);
lean_dec(v_unused_3280_);
v_unused_3281_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3281_);
v___x_3254_ = v_l_2833_;
v_isShared_3255_ = v_isSharedCheck_3276_;
goto v_resetjp_3253_;
}
else
{
lean_dec(v_l_2833_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3276_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
if (lean_obj_tag(v_r_3017_) == 0)
{
lean_object* v_k_3256_; lean_object* v_v_3257_; lean_object* v_size_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v_k_3256_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_k_3256_);
v_v_3257_ = lean_ctor_get(v___x_3169_, 1);
lean_inc(v_v_3257_);
lean_dec_ref(v___x_3169_);
v_size_3258_ = lean_ctor_get(v_r_3017_, 0);
v___x_3259_ = lean_nat_add(v___x_3023_, v_size_3013_);
lean_dec(v_size_3013_);
v___x_3260_ = lean_nat_add(v___x_3023_, v_size_3258_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_tree_3170_);
lean_ctor_set(v___x_3167_, 3, v_r_3017_);
lean_ctor_set(v___x_3167_, 2, v_v_3257_);
lean_ctor_set(v___x_3167_, 1, v_k_3256_);
lean_ctor_set(v___x_3167_, 0, v___x_3260_);
v___x_3262_ = v___x_3167_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_k_3256_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_v_3257_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_r_3017_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v_tree_3170_);
v___x_3262_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3264_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 4, v___x_3262_);
lean_ctor_set(v___x_3254_, 0, v___x_3259_);
v___x_3264_ = v___x_3254_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
else
{
lean_object* v_k_3267_; lean_object* v_v_3268_; lean_object* v___x_3269_; lean_object* v___x_3271_; 
lean_dec(v_size_3013_);
v_k_3267_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_k_3267_);
v_v_3268_ = lean_ctor_get(v___x_3169_, 1);
lean_inc(v_v_3268_);
lean_dec_ref(v___x_3169_);
v___x_3269_ = lean_unsigned_to_nat(3u);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_r_3017_);
lean_ctor_set(v___x_3167_, 3, v_r_3017_);
lean_ctor_set(v___x_3167_, 2, v_v_3268_);
lean_ctor_set(v___x_3167_, 1, v_k_3267_);
lean_ctor_set(v___x_3167_, 0, v___x_3023_);
v___x_3271_ = v___x_3167_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v_k_3267_);
lean_ctor_set(v_reuseFailAlloc_3275_, 2, v_v_3268_);
lean_ctor_set(v_reuseFailAlloc_3275_, 3, v_r_3017_);
lean_ctor_set(v_reuseFailAlloc_3275_, 4, v_r_3017_);
v___x_3271_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
lean_object* v___x_3273_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 4, v___x_3271_);
lean_ctor_set(v___x_3254_, 0, v___x_3269_);
v___x_3273_ = v___x_3254_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3274_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3274_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3274_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3274_, 4, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_3017_) == 0)
{
lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3306_; 
lean_inc(v_l_3016_);
lean_inc(v_v_3015_);
lean_inc(v_k_3014_);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; 
v_unused_3307_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3307_);
v_unused_3308_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_l_2833_, 2);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_2833_, 1);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3311_);
v___x_3283_ = v_l_2833_;
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
else
{
lean_dec(v_l_2833_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3306_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v_k_3285_; lean_object* v_v_3286_; lean_object* v_k_3287_; lean_object* v_v_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3302_; 
v_k_3285_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_k_3285_);
v_v_3286_ = lean_ctor_get(v___x_3169_, 1);
lean_inc(v_v_3286_);
lean_dec_ref(v___x_3169_);
v_k_3287_ = lean_ctor_get(v_r_3017_, 1);
v_v_3288_ = lean_ctor_get(v_r_3017_, 2);
v_isSharedCheck_3302_ = !lean_is_exclusive(v_r_3017_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; 
v_unused_3303_ = lean_ctor_get(v_r_3017_, 4);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_r_3017_, 3);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_r_3017_, 0);
lean_dec(v_unused_3305_);
v___x_3290_ = v_r_3017_;
v_isShared_3291_ = v_isSharedCheck_3302_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_v_3288_);
lean_inc(v_k_3287_);
lean_dec(v_r_3017_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3302_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3292_ = lean_unsigned_to_nat(3u);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 4, v_l_3016_);
lean_ctor_set(v___x_3290_, 3, v_l_3016_);
lean_ctor_set(v___x_3290_, 2, v_v_3015_);
lean_ctor_set(v___x_3290_, 1, v_k_3014_);
lean_ctor_set(v___x_3290_, 0, v___x_3023_);
v___x_3294_ = v___x_3290_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3014_);
lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3015_);
lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_l_3016_);
v___x_3294_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_l_3016_);
lean_ctor_set(v___x_3167_, 3, v_l_3016_);
lean_ctor_set(v___x_3167_, 2, v_v_3286_);
lean_ctor_set(v___x_3167_, 1, v_k_3285_);
lean_ctor_set(v___x_3167_, 0, v___x_3023_);
v___x_3296_ = v___x_3167_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3285_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3286_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v_l_3016_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_l_3016_);
v___x_3296_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 4, v___x_3296_);
lean_ctor_set(v___x_3283_, 3, v___x_3294_);
lean_ctor_set(v___x_3283_, 2, v_v_3288_);
lean_ctor_set(v___x_3283_, 1, v_k_3287_);
lean_ctor_set(v___x_3283_, 0, v___x_3292_);
v___x_3298_ = v___x_3283_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v_k_3287_);
lean_ctor_set(v_reuseFailAlloc_3299_, 2, v_v_3288_);
lean_ctor_set(v_reuseFailAlloc_3299_, 3, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3299_, 4, v___x_3296_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
}
else
{
lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
v_k_3312_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_k_3312_);
v_v_3313_ = lean_ctor_get(v___x_3169_, 1);
lean_inc(v_v_3313_);
lean_dec_ref(v___x_3169_);
v___x_3314_ = lean_unsigned_to_nat(2u);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 4, v_r_3017_);
lean_ctor_set(v___x_3167_, 3, v_l_2833_);
lean_ctor_set(v___x_3167_, 2, v_v_3313_);
lean_ctor_set(v___x_3167_, 1, v_k_3312_);
lean_ctor_set(v___x_3167_, 0, v___x_3314_);
v___x_3316_ = v___x_3167_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_k_3312_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_v_3313_);
lean_ctor_set(v_reuseFailAlloc_3317_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3317_, 4, v_r_3017_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
}
}
else
{
return v_l_2833_;
}
}
else
{
return v_r_2834_;
}
}
default: 
{
lean_object* v_impl_3324_; lean_object* v___x_3325_; 
v_impl_3324_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_2829_, v_r_2834_);
v___x_3325_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_3324_) == 0)
{
if (lean_obj_tag(v_l_2833_) == 0)
{
lean_object* v_size_3326_; lean_object* v_size_3327_; lean_object* v_k_3328_; lean_object* v_v_3329_; lean_object* v_l_3330_; lean_object* v_r_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; 
v_size_3326_ = lean_ctor_get(v_impl_3324_, 0);
v_size_3327_ = lean_ctor_get(v_l_2833_, 0);
v_k_3328_ = lean_ctor_get(v_l_2833_, 1);
v_v_3329_ = lean_ctor_get(v_l_2833_, 2);
v_l_3330_ = lean_ctor_get(v_l_2833_, 3);
v_r_3331_ = lean_ctor_get(v_l_2833_, 4);
lean_inc(v_r_3331_);
v___x_3332_ = lean_unsigned_to_nat(3u);
v___x_3333_ = lean_nat_mul(v___x_3332_, v_size_3326_);
v___x_3334_ = lean_nat_dec_lt(v___x_3333_, v_size_3327_);
lean_dec(v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
lean_dec(v_r_3331_);
v___x_3335_ = lean_nat_add(v___x_3325_, v_size_3327_);
v___x_3336_ = lean_nat_add(v___x_3335_, v_size_3326_);
lean_dec(v___x_3335_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_impl_3324_);
lean_ctor_set(v___x_2836_, 0, v___x_3336_);
v___x_3338_ = v___x_2836_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v_impl_3324_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
else
{
lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3405_; 
lean_inc(v_l_3330_);
lean_inc(v_v_3329_);
lean_inc(v_k_3328_);
lean_inc(v_size_3327_);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; lean_object* v_unused_3407_; lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; 
v_unused_3406_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3406_);
v_unused_3407_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3407_);
v_unused_3408_ = lean_ctor_get(v_l_2833_, 2);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_l_2833_, 1);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3410_);
v___x_3341_ = v_l_2833_;
v_isShared_3342_ = v_isSharedCheck_3405_;
goto v_resetjp_3340_;
}
else
{
lean_dec(v_l_2833_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3405_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_size_3343_; lean_object* v_size_3344_; lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v_l_3347_; lean_object* v_r_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v_size_3343_ = lean_ctor_get(v_l_3330_, 0);
v_size_3344_ = lean_ctor_get(v_r_3331_, 0);
v_k_3345_ = lean_ctor_get(v_r_3331_, 1);
v_v_3346_ = lean_ctor_get(v_r_3331_, 2);
v_l_3347_ = lean_ctor_get(v_r_3331_, 3);
v_r_3348_ = lean_ctor_get(v_r_3331_, 4);
v___x_3349_ = lean_unsigned_to_nat(2u);
v___x_3350_ = lean_nat_mul(v___x_3349_, v_size_3343_);
v___x_3351_ = lean_nat_dec_lt(v_size_3344_, v___x_3350_);
lean_dec(v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3380_; 
lean_inc(v_r_3348_);
lean_inc(v_l_3347_);
lean_inc(v_v_3346_);
lean_inc(v_k_3345_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_r_3331_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; lean_object* v_unused_3382_; lean_object* v_unused_3383_; lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3381_ = lean_ctor_get(v_r_3331_, 4);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_r_3331_, 3);
lean_dec(v_unused_3382_);
v_unused_3383_ = lean_ctor_get(v_r_3331_, 2);
lean_dec(v_unused_3383_);
v_unused_3384_ = lean_ctor_get(v_r_3331_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_r_3331_, 0);
lean_dec(v_unused_3385_);
v___x_3353_ = v_r_3331_;
v_isShared_3354_ = v_isSharedCheck_3380_;
goto v_resetjp_3352_;
}
else
{
lean_dec(v_r_3331_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3380_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___x_3368_; lean_object* v___y_3370_; 
v___x_3355_ = lean_nat_add(v___x_3325_, v_size_3327_);
lean_dec(v_size_3327_);
v___x_3356_ = lean_nat_add(v___x_3355_, v_size_3326_);
lean_dec(v___x_3355_);
v___x_3368_ = lean_nat_add(v___x_3325_, v_size_3343_);
if (lean_obj_tag(v_l_3347_) == 0)
{
lean_object* v_size_3378_; 
v_size_3378_ = lean_ctor_get(v_l_3347_, 0);
lean_inc(v_size_3378_);
v___y_3370_ = v_size_3378_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_unsigned_to_nat(0u);
v___y_3370_ = v___x_3379_;
goto v___jp_3369_;
}
v___jp_3357_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = lean_nat_add(v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_impl_3324_);
lean_ctor_set(v___x_3353_, 3, v_r_3348_);
lean_ctor_set(v___x_3353_, 2, v_v_2832_);
lean_ctor_set(v___x_3353_, 1, v_k_2831_);
lean_ctor_set(v___x_3353_, 0, v___x_3361_);
v___x_3363_ = v___x_3353_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3361_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v_r_3348_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v_impl_3324_);
v___x_3363_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 4, v___x_3363_);
lean_ctor_set(v___x_3341_, 3, v___y_3358_);
lean_ctor_set(v___x_3341_, 2, v_v_3346_);
lean_ctor_set(v___x_3341_, 1, v_k_3345_);
lean_ctor_set(v___x_3341_, 0, v___x_3356_);
v___x_3365_ = v___x_3341_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_k_3345_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_v_3346_);
lean_ctor_set(v_reuseFailAlloc_3366_, 3, v___y_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 4, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
v___jp_3369_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_nat_add(v___x_3368_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec(v___x_3368_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_l_3347_);
lean_ctor_set(v___x_2836_, 3, v_l_3330_);
lean_ctor_set(v___x_2836_, 2, v_v_3329_);
lean_ctor_set(v___x_2836_, 1, v_k_3328_);
lean_ctor_set(v___x_2836_, 0, v___x_3371_);
v___x_3373_ = v___x_2836_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v_l_3347_);
v___x_3373_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; 
v___x_3374_ = lean_nat_add(v___x_3325_, v_size_3326_);
if (lean_obj_tag(v_r_3348_) == 0)
{
lean_object* v_size_3375_; 
v_size_3375_ = lean_ctor_get(v_r_3348_, 0);
lean_inc(v_size_3375_);
v___y_3358_ = v___x_3373_;
v___y_3359_ = v___x_3374_;
v___y_3360_ = v_size_3375_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_unsigned_to_nat(0u);
v___y_3358_ = v___x_3373_;
v___y_3359_ = v___x_3374_;
v___y_3360_ = v___x_3376_;
goto v___jp_3357_;
}
}
}
}
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3391_; 
lean_del_object(v___x_2836_);
v___x_3386_ = lean_nat_add(v___x_3325_, v_size_3327_);
lean_dec(v_size_3327_);
v___x_3387_ = lean_nat_add(v___x_3386_, v_size_3326_);
lean_dec(v___x_3386_);
v___x_3388_ = lean_nat_add(v___x_3325_, v_size_3326_);
v___x_3389_ = lean_nat_add(v___x_3388_, v_size_3344_);
lean_dec(v___x_3388_);
lean_inc_ref(v_impl_3324_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 4, v_impl_3324_);
lean_ctor_set(v___x_3341_, 3, v_r_3331_);
lean_ctor_set(v___x_3341_, 2, v_v_2832_);
lean_ctor_set(v___x_3341_, 1, v_k_2831_);
lean_ctor_set(v___x_3341_, 0, v___x_3389_);
v___x_3391_ = v___x_3341_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3404_, 3, v_r_3331_);
lean_ctor_set(v_reuseFailAlloc_3404_, 4, v_impl_3324_);
v___x_3391_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
v_isSharedCheck_3398_ = !lean_is_exclusive(v_impl_3324_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; lean_object* v_unused_3400_; lean_object* v_unused_3401_; lean_object* v_unused_3402_; lean_object* v_unused_3403_; 
v_unused_3399_ = lean_ctor_get(v_impl_3324_, 4);
lean_dec(v_unused_3399_);
v_unused_3400_ = lean_ctor_get(v_impl_3324_, 3);
lean_dec(v_unused_3400_);
v_unused_3401_ = lean_ctor_get(v_impl_3324_, 2);
lean_dec(v_unused_3401_);
v_unused_3402_ = lean_ctor_get(v_impl_3324_, 1);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_impl_3324_, 0);
lean_dec(v_unused_3403_);
v___x_3393_ = v_impl_3324_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_dec(v_impl_3324_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v___x_3391_);
lean_ctor_set(v___x_3393_, 3, v_l_3330_);
lean_ctor_set(v___x_3393_, 2, v_v_3329_);
lean_ctor_set(v___x_3393_, 1, v_k_3328_);
lean_ctor_set(v___x_3393_, 0, v___x_3387_);
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3328_);
lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3329_);
lean_ctor_set(v_reuseFailAlloc_3397_, 3, v_l_3330_);
lean_ctor_set(v_reuseFailAlloc_3397_, 4, v___x_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v_size_3411_ = lean_ctor_get(v_impl_3324_, 0);
v___x_3412_ = lean_nat_add(v___x_3325_, v_size_3411_);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_impl_3324_);
lean_ctor_set(v___x_2836_, 0, v___x_3412_);
v___x_3414_ = v___x_2836_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_impl_3324_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
else
{
if (lean_obj_tag(v_l_2833_) == 0)
{
lean_object* v_l_3416_; 
v_l_3416_ = lean_ctor_get(v_l_2833_, 3);
if (lean_obj_tag(v_l_3416_) == 0)
{
lean_object* v_r_3417_; 
lean_inc_ref(v_l_3416_);
v_r_3417_ = lean_ctor_get(v_l_2833_, 4);
lean_inc(v_r_3417_);
if (lean_obj_tag(v_r_3417_) == 0)
{
lean_object* v_size_3418_; lean_object* v_k_3419_; lean_object* v_v_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3433_; 
v_size_3418_ = lean_ctor_get(v_l_2833_, 0);
v_k_3419_ = lean_ctor_get(v_l_2833_, 1);
v_v_3420_ = lean_ctor_get(v_l_2833_, 2);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; lean_object* v_unused_3435_; 
v_unused_3434_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3435_);
v___x_3422_ = v_l_2833_;
v_isShared_3423_ = v_isSharedCheck_3433_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_v_3420_);
lean_inc(v_k_3419_);
lean_inc(v_size_3418_);
lean_dec(v_l_2833_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3433_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_size_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v_size_3424_ = lean_ctor_get(v_r_3417_, 0);
v___x_3425_ = lean_nat_add(v___x_3325_, v_size_3418_);
lean_dec(v_size_3418_);
v___x_3426_ = lean_nat_add(v___x_3325_, v_size_3424_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 4, v_impl_3324_);
lean_ctor_set(v___x_3422_, 3, v_r_3417_);
lean_ctor_set(v___x_3422_, 2, v_v_2832_);
lean_ctor_set(v___x_3422_, 1, v_k_2831_);
lean_ctor_set(v___x_3422_, 0, v___x_3426_);
v___x_3428_ = v___x_3422_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3426_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3432_, 3, v_r_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 4, v_impl_3324_);
v___x_3428_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_3428_);
lean_ctor_set(v___x_2836_, 3, v_l_3416_);
lean_ctor_set(v___x_2836_, 2, v_v_3420_);
lean_ctor_set(v___x_2836_, 1, v_k_3419_);
lean_ctor_set(v___x_2836_, 0, v___x_3425_);
v___x_3430_ = v___x_2836_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3425_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3419_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3420_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_l_3416_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_k_3436_; lean_object* v_v_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3448_; 
v_k_3436_ = lean_ctor_get(v_l_2833_, 1);
v_v_3437_ = lean_ctor_get(v_l_2833_, 2);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3448_ == 0)
{
lean_object* v_unused_3449_; lean_object* v_unused_3450_; lean_object* v_unused_3451_; 
v_unused_3449_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3449_);
v_unused_3450_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3451_);
v___x_3439_ = v_l_2833_;
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_v_3437_);
lean_inc(v_k_3436_);
lean_dec(v_l_2833_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3448_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = lean_unsigned_to_nat(3u);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 3, v_r_3417_);
lean_ctor_set(v___x_3439_, 2, v_v_2832_);
lean_ctor_set(v___x_3439_, 1, v_k_2831_);
lean_ctor_set(v___x_3439_, 0, v___x_3325_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3447_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3447_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3447_, 3, v_r_3417_);
lean_ctor_set(v_reuseFailAlloc_3447_, 4, v_r_3417_);
v___x_3443_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3445_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_3443_);
lean_ctor_set(v___x_2836_, 3, v_l_3416_);
lean_ctor_set(v___x_2836_, 2, v_v_3437_);
lean_ctor_set(v___x_2836_, 1, v_k_3436_);
lean_ctor_set(v___x_2836_, 0, v___x_3441_);
v___x_3445_ = v___x_2836_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_k_3436_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v_v_3437_);
lean_ctor_set(v_reuseFailAlloc_3446_, 3, v_l_3416_);
lean_ctor_set(v_reuseFailAlloc_3446_, 4, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
}
else
{
lean_object* v_r_3452_; 
v_r_3452_ = lean_ctor_get(v_l_2833_, 4);
lean_inc(v_r_3452_);
if (lean_obj_tag(v_r_3452_) == 0)
{
lean_object* v_k_3453_; lean_object* v_v_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3477_; 
lean_inc(v_l_3416_);
v_k_3453_ = lean_ctor_get(v_l_2833_, 1);
v_v_3454_ = lean_ctor_get(v_l_2833_, 2);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_l_2833_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; lean_object* v_unused_3479_; lean_object* v_unused_3480_; 
v_unused_3478_ = lean_ctor_get(v_l_2833_, 4);
lean_dec(v_unused_3478_);
v_unused_3479_ = lean_ctor_get(v_l_2833_, 3);
lean_dec(v_unused_3479_);
v_unused_3480_ = lean_ctor_get(v_l_2833_, 0);
lean_dec(v_unused_3480_);
v___x_3456_ = v_l_2833_;
v_isShared_3457_ = v_isSharedCheck_3477_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_v_3454_);
lean_inc(v_k_3453_);
lean_dec(v_l_2833_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3477_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_k_3458_; lean_object* v_v_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3473_; 
v_k_3458_ = lean_ctor_get(v_r_3452_, 1);
v_v_3459_ = lean_ctor_get(v_r_3452_, 2);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_r_3452_);
if (v_isSharedCheck_3473_ == 0)
{
lean_object* v_unused_3474_; lean_object* v_unused_3475_; lean_object* v_unused_3476_; 
v_unused_3474_ = lean_ctor_get(v_r_3452_, 4);
lean_dec(v_unused_3474_);
v_unused_3475_ = lean_ctor_get(v_r_3452_, 3);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_r_3452_, 0);
lean_dec(v_unused_3476_);
v___x_3461_ = v_r_3452_;
v_isShared_3462_ = v_isSharedCheck_3473_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_v_3459_);
lean_inc(v_k_3458_);
lean_dec(v_r_3452_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3473_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_unsigned_to_nat(3u);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 4, v_l_3416_);
lean_ctor_set(v___x_3461_, 3, v_l_3416_);
lean_ctor_set(v___x_3461_, 2, v_v_3454_);
lean_ctor_set(v___x_3461_, 1, v_k_3453_);
lean_ctor_set(v___x_3461_, 0, v___x_3325_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_k_3453_);
lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_v_3454_);
lean_ctor_set(v_reuseFailAlloc_3472_, 3, v_l_3416_);
lean_ctor_set(v_reuseFailAlloc_3472_, 4, v_l_3416_);
v___x_3465_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 4, v_l_3416_);
lean_ctor_set(v___x_3456_, 2, v_v_2832_);
lean_ctor_set(v___x_3456_, 1, v_k_2831_);
lean_ctor_set(v___x_3456_, 0, v___x_3325_);
v___x_3467_ = v___x_3456_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_l_3416_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_l_3416_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3469_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_3467_);
lean_ctor_set(v___x_2836_, 3, v___x_3465_);
lean_ctor_set(v___x_2836_, 2, v_v_3459_);
lean_ctor_set(v___x_2836_, 1, v_k_3458_);
lean_ctor_set(v___x_2836_, 0, v___x_3463_);
v___x_3469_ = v___x_2836_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3458_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3459_);
lean_ctor_set(v_reuseFailAlloc_3470_, 3, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3470_, 4, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3481_ = lean_unsigned_to_nat(2u);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_r_3452_);
lean_ctor_set(v___x_2836_, 0, v___x_3481_);
v___x_3483_ = v___x_2836_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3484_, 4, v_r_3452_);
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
lean_object* v___x_3486_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v_l_2833_);
lean_ctor_set(v___x_2836_, 0, v___x_3325_);
v___x_3486_ = v___x_2836_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_2831_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_2832_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_l_2833_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_l_2833_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
}
}
else
{
return v_t_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg___boxed(lean_object* v_k_3490_, lean_object* v_t_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3490_, v_t_3491_);
lean_dec(v_k_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(lean_object* v_declName_3493_, lean_object* v_ps_3494_){
_start:
{
lean_object* v_importedEntries_3495_; lean_object* v_state_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3504_; 
v_importedEntries_3495_ = lean_ctor_get(v_ps_3494_, 0);
v_state_3496_ = lean_ctor_get(v_ps_3494_, 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_ps_3494_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3498_ = v_ps_3494_;
v_isShared_3499_ = v_isSharedCheck_3504_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_state_3496_);
lean_inc(v_importedEntries_3495_);
lean_dec(v_ps_3494_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3504_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v___x_3502_; 
v___x_3500_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_declName_3493_, v_state_3496_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v___x_3500_);
v___x_3502_ = v___x_3498_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_importedEntries_3495_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v___x_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed(lean_object* v_declName_3505_, lean_object* v_ps_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0(v_declName_3505_, v_ps_3506_);
lean_dec(v_declName_3505_);
return v_res_3507_;
}
}
static lean_object* _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__0));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(lean_object* v_declName_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___f_3551_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___x_3574_; lean_object* v_env_3575_; lean_object* v___x_3576_; 
lean_inc(v_declName_3511_);
v___f_3551_ = lean_alloc_closure((void*)(l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3551_, 0, v_declName_3511_);
v___x_3574_ = lean_st_ref_get(v___y_3517_);
v_env_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc_ref(v_env_3575_);
lean_dec(v___x_3574_);
v___x_3576_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3575_, v_declName_3511_);
lean_dec_ref(v_env_3575_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_dec(v_declName_3511_);
v___y_3553_ = v___y_3515_;
v___y_3554_ = v___y_3517_;
goto v___jp_3552_;
}
else
{
uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec_ref_known(v___x_3576_, 1);
lean_dec_ref(v___f_3551_);
v___x_3577_ = 0;
v___x_3578_ = lean_obj_once(&l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1, &l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1_once, _init_l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___closed__1);
v___x_3579_ = l_Lean_MessageData_ofConstName(v_declName_3511_, v___x_3577_);
v___x_3580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = lean_obj_once(&l_Lean_addMarkdownDocString___redArg___lam__5___closed__3, &l_Lean_addMarkdownDocString___redArg___lam__5___closed__3_once, _init_l_Lean_addMarkdownDocString___redArg___lam__5___closed__3);
v___x_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3580_);
lean_ctor_set(v___x_3582_, 1, v___x_3581_);
v___x_3583_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3582_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
return v___x_3583_;
}
v___jp_3519_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v_mctx_3535_; lean_object* v_zetaDeltaFVarIds_3536_; lean_object* v_postponed_3537_; lean_object* v_diag_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3549_; 
v___x_3531_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
v___x_3532_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3532_, 0, v___y_3530_);
lean_ctor_set(v___x_3532_, 1, v___y_3527_);
lean_ctor_set(v___x_3532_, 2, v___y_3528_);
lean_ctor_set(v___x_3532_, 3, v___y_3529_);
lean_ctor_set(v___x_3532_, 4, v___y_3523_);
lean_ctor_set(v___x_3532_, 5, v___x_3531_);
lean_ctor_set(v___x_3532_, 6, v___y_3522_);
lean_ctor_set(v___x_3532_, 7, v___y_3526_);
lean_ctor_set(v___x_3532_, 8, v___y_3525_);
lean_ctor_set(v___x_3532_, 9, v___y_3524_);
v___x_3533_ = lean_st_ref_put(v___y_3521_, v___x_3532_);
v___x_3534_ = lean_st_ref_take(v___y_3520_);
v_mctx_3535_ = lean_ctor_get(v___x_3534_, 0);
v_zetaDeltaFVarIds_3536_ = lean_ctor_get(v___x_3534_, 2);
v_postponed_3537_ = lean_ctor_get(v___x_3534_, 3);
v_diag_3538_ = lean_ctor_get(v___x_3534_, 4);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v___x_3534_, 1);
lean_dec(v_unused_3550_);
v___x_3540_ = v___x_3534_;
v_isShared_3541_ = v_isSharedCheck_3549_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_diag_3538_);
lean_inc(v_postponed_3537_);
lean_inc(v_zetaDeltaFVarIds_3536_);
lean_inc(v_mctx_3535_);
lean_dec(v___x_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3549_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 1, v___x_3543_);
v___x_3545_ = v___x_3540_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_mctx_3535_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_zetaDeltaFVarIds_3536_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_postponed_3537_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_diag_3538_);
v___x_3545_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_st_ref_put(v___y_3520_, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3542_);
return v___x_3547_;
}
}
}
v___jp_3552_:
{
lean_object* v___x_3555_; lean_object* v_env_3556_; lean_object* v_nextMacroScope_3557_; lean_object* v_ngen_3558_; lean_object* v_auxDeclNGen_3559_; lean_object* v_traceState_3560_; lean_object* v_recordedDeps_3561_; lean_object* v_messages_3562_; lean_object* v_infoState_3563_; lean_object* v_snapshotTasks_3564_; lean_object* v___x_3565_; lean_object* v_toEnvExtension_3566_; uint8_t v_logWrites_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3555_ = lean_st_ref_take(v___y_3554_);
v_env_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc_ref(v_env_3556_);
v_nextMacroScope_3557_ = lean_ctor_get(v___x_3555_, 1);
lean_inc(v_nextMacroScope_3557_);
v_ngen_3558_ = lean_ctor_get(v___x_3555_, 2);
lean_inc_ref(v_ngen_3558_);
v_auxDeclNGen_3559_ = lean_ctor_get(v___x_3555_, 3);
lean_inc_ref(v_auxDeclNGen_3559_);
v_traceState_3560_ = lean_ctor_get(v___x_3555_, 4);
lean_inc_ref(v_traceState_3560_);
v_recordedDeps_3561_ = lean_ctor_get(v___x_3555_, 6);
lean_inc_ref(v_recordedDeps_3561_);
v_messages_3562_ = lean_ctor_get(v___x_3555_, 7);
lean_inc_ref(v_messages_3562_);
v_infoState_3563_ = lean_ctor_get(v___x_3555_, 8);
lean_inc_ref(v_infoState_3563_);
v_snapshotTasks_3564_ = lean_ctor_get(v___x_3555_, 9);
lean_inc_ref(v_snapshotTasks_3564_);
lean_dec(v___x_3555_);
v___x_3565_ = l_Lean_docStringExt;
v_toEnvExtension_3566_ = lean_ctor_get(v___x_3565_, 0);
v_logWrites_3567_ = lean_ctor_get_uint8(v_toEnvExtension_3566_, sizeof(void*)*6);
v___x_3568_ = lean_box(2);
v___x_3569_ = lean_box(0);
v___x_3570_ = 1;
if (v_logWrites_3567_ == 0)
{
lean_object* v___x_3571_; 
lean_inc_ref(v_toEnvExtension_3566_);
v___x_3571_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3566_, v_env_3556_, v___f_3551_, v___x_3568_, v___x_3569_, v___x_3570_);
v___y_3520_ = v___y_3553_;
v___y_3521_ = v___y_3554_;
v___y_3522_ = v_recordedDeps_3561_;
v___y_3523_ = v_traceState_3560_;
v___y_3524_ = v_snapshotTasks_3564_;
v___y_3525_ = v_infoState_3563_;
v___y_3526_ = v_messages_3562_;
v___y_3527_ = v_nextMacroScope_3557_;
v___y_3528_ = v_ngen_3558_;
v___y_3529_ = v_auxDeclNGen_3559_;
v___y_3530_ = v___x_3571_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_inc_ref_n(v_toEnvExtension_3566_, 2);
v___x_3572_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3566_, v_env_3556_);
lean_dec_ref(v_env_3556_);
v___x_3573_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3566_, v___x_3572_, v___f_3551_, v___x_3568_, v___x_3569_, v___x_3570_);
v___y_3520_ = v___y_3553_;
v___y_3521_ = v___y_3554_;
v___y_3522_ = v_recordedDeps_3561_;
v___y_3523_ = v_traceState_3560_;
v___y_3524_ = v_snapshotTasks_3564_;
v___y_3525_ = v_infoState_3563_;
v___y_3526_ = v_messages_3562_;
v___y_3527_ = v_nextMacroScope_3557_;
v___y_3528_ = v_ngen_3558_;
v___y_3529_ = v_auxDeclNGen_3559_;
v___y_3530_ = v___x_3573_;
goto v___jp_3519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0___boxed(lean_object* v_declName_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
return v_res_3592_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__1(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__0));
v___x_3595_ = l_Lean_stringToMessageData(v___x_3594_);
return v___x_3595_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__3(void){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3597_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__2));
v___x_3598_ = l_Lean_stringToMessageData(v___x_3597_);
return v___x_3598_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__5(void){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__4));
v___x_3601_ = l_Lean_stringToMessageData(v___x_3600_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lean_makeDocStringVerso___closed__7(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_makeDocStringVerso___closed__6));
v___x_3604_ = l_Lean_stringToMessageData(v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso(lean_object* v_declName_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v___x_3613_; lean_object* v_env_3614_; lean_object* v_ref_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3613_ = lean_st_ref_get(v_a_3611_);
v_env_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_ref(v_env_3614_);
lean_dec(v___x_3613_);
v_ref_3615_ = lean_ctor_get(v_a_3610_, 2);
v___x_3616_ = 1;
lean_inc(v_declName_3605_);
v___x_3617_ = l_Lean_findInternalDocString_x3f(v_env_3614_, v_declName_3605_, v___x_3616_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
if (lean_obj_tag(v_a_3618_) == 1)
{
lean_object* v_val_3619_; 
v_val_3619_ = lean_ctor_get(v_a_3618_, 0);
lean_inc(v_val_3619_);
lean_dec_ref_known(v_a_3618_, 1);
if (lean_obj_tag(v_val_3619_) == 0)
{
lean_object* v_val_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3641_; 
v_val_3620_ = lean_ctor_get(v_val_3619_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_val_3619_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3622_ = v_val_3619_;
v_isShared_3623_ = v_isSharedCheck_3641_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_val_3620_);
lean_dec(v_val_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3641_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_removeBuiltinDocString(v_declName_3605_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v___x_3625_; 
lean_dec_ref_known(v___x_3624_, 1);
lean_del_object(v___x_3622_);
lean_inc(v_declName_3605_);
v___x_3625_ = l_Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0(v_declName_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref_known(v___x_3625_, 1);
v___x_3626_ = l_Lean_addVersoDocStringFromString(v_declName_3605_, v_val_3620_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
return v___x_3626_;
}
else
{
lean_dec(v_val_3620_);
lean_dec(v_declName_3605_);
return v___x_3625_;
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3640_; 
lean_dec(v_val_3620_);
lean_dec(v_declName_3605_);
v_a_3627_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3629_ = v___x_3624_;
v_isShared_3630_ = v_isSharedCheck_3640_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3624_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3640_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = lean_io_error_to_string(v_a_3627_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 3);
lean_ctor_set(v___x_3622_, 0, v___x_3631_);
v___x_3633_ = v___x_3622_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3634_ = l_Lean_MessageData_ofFormat(v___x_3633_);
lean_inc(v_ref_3615_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v_ref_3615_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3635_);
v___x_3637_ = v___x_3629_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
}
else
{
lean_object* v___x_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec(v_val_3619_);
v___x_3642_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__1, &l_Lean_makeDocStringVerso___closed__1_once, _init_l_Lean_makeDocStringVerso___closed__1);
v___x_3643_ = 0;
v___x_3644_ = l_Lean_MessageData_ofConstName(v_declName_3605_, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__3, &l_Lean_makeDocStringVerso___closed__3_once, _init_l_Lean_makeDocStringVerso___closed__3);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3647_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
return v___x_3648_;
}
}
else
{
lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
lean_dec(v_a_3618_);
v___x_3649_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__5, &l_Lean_makeDocStringVerso___closed__5_once, _init_l_Lean_makeDocStringVerso___closed__5);
v___x_3650_ = 0;
v___x_3651_ = l_Lean_MessageData_ofConstName(v_declName_3605_, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3649_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_obj_once(&l_Lean_makeDocStringVerso___closed__7, &l_Lean_makeDocStringVerso___closed__7_once, _init_l_Lean_makeDocStringVerso___closed__7);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3654_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
return v___x_3655_;
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_declName_3605_);
v_a_3656_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3658_ = v___x_3617_;
v_isShared_3659_ = v_isSharedCheck_3667_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3617_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3667_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3660_ = lean_io_error_to_string(v_a_3656_);
v___x_3661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
v___x_3662_ = l_Lean_MessageData_ofFormat(v___x_3661_);
lean_inc(v_ref_3615_);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_ref_3615_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3663_);
v___x_3665_ = v___x_3658_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_makeDocStringVerso___boxed(lean_object* v_declName_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_makeDocStringVerso(v_declName_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(lean_object* v_00_u03b2_3677_, lean_object* v_k_3678_, lean_object* v_t_3679_, lean_object* v_h_3680_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___redArg(v_k_3678_, v_t_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3682_, lean_object* v_k_3683_, lean_object* v_t_3684_, lean_object* v_h_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_removeDocStringCore___at___00Lean_makeDocStringVerso_spec__0_spec__0(v_00_u03b2_3682_, v_k_3683_, v_t_3684_, v_h_3685_);
lean_dec(v_k_3683_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* v_declName_3687_, lean_object* v_binders_3688_, lean_object* v_docComment_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
uint8_t v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = l_Lean_isVersoDocComment(v_docComment_3689_);
v___x_3698_ = l_Lean_addDocStringOf(v___x_3697_, v_declName_3687_, v_binders_3688_, v_docComment_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___boxed(lean_object* v_declName_3699_, lean_object* v_binders_3700_, lean_object* v_docComment_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_addDocString(v_declName_3699_, v_binders_3700_, v_docComment_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* v_declName_3710_, lean_object* v_binders_3711_, lean_object* v_docString_x3f_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
if (lean_obj_tag(v_docString_x3f_3712_) == 0)
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_dec(v_binders_3711_);
lean_dec(v_declName_3710_);
v___x_3720_ = lean_box(0);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3720_);
return v___x_3721_;
}
else
{
lean_object* v_val_3722_; lean_object* v___x_3723_; 
v_val_3722_ = lean_ctor_get(v_docString_x3f_3712_, 0);
lean_inc(v_val_3722_);
lean_dec_ref_known(v_docString_x3f_3712_, 1);
v___x_3723_ = l_Lean_addDocString(v_declName_3710_, v_binders_3711_, v_val_3722_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
return v___x_3723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___boxed(lean_object* v_declName_3724_, lean_object* v_binders_3725_, lean_object* v_docString_x3f_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_addDocString_x27(v_declName_3724_, v_binders_3725_, v_docString_x3f_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(lean_object* v_env_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; lean_object* v_nextMacroScope_3740_; lean_object* v_ngen_3741_; lean_object* v_auxDeclNGen_3742_; lean_object* v_traceState_3743_; lean_object* v_recordedDeps_3744_; lean_object* v_messages_3745_; lean_object* v_infoState_3746_; lean_object* v_snapshotTasks_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3773_; 
v___x_3739_ = lean_st_ref_take(v___y_3737_);
v_nextMacroScope_3740_ = lean_ctor_get(v___x_3739_, 1);
v_ngen_3741_ = lean_ctor_get(v___x_3739_, 2);
v_auxDeclNGen_3742_ = lean_ctor_get(v___x_3739_, 3);
v_traceState_3743_ = lean_ctor_get(v___x_3739_, 4);
v_recordedDeps_3744_ = lean_ctor_get(v___x_3739_, 6);
v_messages_3745_ = lean_ctor_get(v___x_3739_, 7);
v_infoState_3746_ = lean_ctor_get(v___x_3739_, 8);
v_snapshotTasks_3747_ = lean_ctor_get(v___x_3739_, 9);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; lean_object* v_unused_3775_; 
v_unused_3774_ = lean_ctor_get(v___x_3739_, 5);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v___x_3739_, 0);
lean_dec(v_unused_3775_);
v___x_3749_ = v___x_3739_;
v_isShared_3750_ = v_isSharedCheck_3773_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_snapshotTasks_3747_);
lean_inc(v_infoState_3746_);
lean_inc(v_messages_3745_);
lean_inc(v_recordedDeps_3744_);
lean_inc(v_traceState_3743_);
lean_inc(v_auxDeclNGen_3742_);
lean_inc(v_ngen_3741_);
lean_inc(v_nextMacroScope_3740_);
lean_dec(v___x_3739_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3773_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__1);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 5, v___x_3751_);
lean_ctor_set(v___x_3749_, 0, v_env_3735_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_env_3735_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_nextMacroScope_3740_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_ngen_3741_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_auxDeclNGen_3742_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_traceState_3743_);
lean_ctor_set(v_reuseFailAlloc_3772_, 5, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3772_, 6, v_recordedDeps_3744_);
lean_ctor_set(v_reuseFailAlloc_3772_, 7, v_messages_3745_);
lean_ctor_set(v_reuseFailAlloc_3772_, 8, v_infoState_3746_);
lean_ctor_set(v_reuseFailAlloc_3772_, 9, v_snapshotTasks_3747_);
v___x_3753_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v_mctx_3756_; lean_object* v_zetaDeltaFVarIds_3757_; lean_object* v_postponed_3758_; lean_object* v_diag_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3770_; 
v___x_3754_ = lean_st_ref_put(v___y_3737_, v___x_3753_);
v___x_3755_ = lean_st_ref_take(v___y_3736_);
v_mctx_3756_ = lean_ctor_get(v___x_3755_, 0);
v_zetaDeltaFVarIds_3757_ = lean_ctor_get(v___x_3755_, 2);
v_postponed_3758_ = lean_ctor_get(v___x_3755_, 3);
v_diag_3759_ = lean_ctor_get(v___x_3755_, 4);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3770_ == 0)
{
lean_object* v_unused_3771_; 
v_unused_3771_ = lean_ctor_get(v___x_3755_, 1);
lean_dec(v_unused_3771_);
v___x_3761_ = v___x_3755_;
v_isShared_3762_ = v_isSharedCheck_3770_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_diag_3759_);
lean_inc(v_postponed_3758_);
lean_inc(v_zetaDeltaFVarIds_3757_);
lean_inc(v_mctx_3756_);
lean_dec(v___x_3755_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3770_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3766_; 
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_obj_once(&l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2, &l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2_once, _init_l_Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0___closed__2);
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 1, v___x_3764_);
v___x_3766_ = v___x_3761_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_mctx_3756_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_zetaDeltaFVarIds_3757_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_postponed_3758_);
lean_ctor_set(v_reuseFailAlloc_3769_, 4, v_diag_3759_);
v___x_3766_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_st_ref_put(v___y_3736_, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3763_);
return v___x_3768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg___boxed(lean_object* v_env_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec(v___y_3777_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(lean_object* v_n_3781_, uint8_t v___x_3782_, lean_object* v_as_3783_, size_t v_i_3784_, size_t v_stop_3785_, lean_object* v_b_3786_){
_start:
{
lean_object* v___y_3788_; uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_eq(v_i_3784_, v_stop_3785_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v_index_3794_; lean_object* v_sourceString_3795_; lean_object* v_imports_3796_; lean_object* v_currNamespace_3797_; lean_object* v_openDecls_3798_; lean_object* v_options_3799_; lean_object* v_check_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3817_; 
v___x_3793_ = lean_array_uget(v_as_3783_, v_i_3784_);
v_index_3794_ = lean_ctor_get(v___x_3793_, 1);
v_sourceString_3795_ = lean_ctor_get(v___x_3793_, 2);
v_imports_3796_ = lean_ctor_get(v___x_3793_, 3);
v_currNamespace_3797_ = lean_ctor_get(v___x_3793_, 4);
v_openDecls_3798_ = lean_ctor_get(v___x_3793_, 5);
v_options_3799_ = lean_ctor_get(v___x_3793_, 6);
v_check_3800_ = lean_ctor_get(v___x_3793_, 7);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; 
v_unused_3818_ = lean_ctor_get(v___x_3793_, 0);
lean_dec(v_unused_3818_);
v___x_3802_ = v___x_3793_;
v_isShared_3803_ = v_isSharedCheck_3817_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_check_3800_);
lean_inc(v_options_3799_);
lean_inc(v_openDecls_3798_);
lean_inc(v_currNamespace_3797_);
lean_inc(v_imports_3796_);
lean_inc(v_sourceString_3795_);
lean_inc(v_index_3794_);
lean_dec(v___x_3793_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3817_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v_toEnvExtension_3805_; lean_object* v_asyncMode_3806_; uint8_t v_logWrites_3807_; lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3804_ = l_Lean_Doc_deferredCheckExt;
v_toEnvExtension_3805_ = lean_ctor_get(v___x_3804_, 0);
v_asyncMode_3806_ = lean_ctor_get(v_toEnvExtension_3805_, 2);
v_logWrites_3807_ = lean_ctor_get_uint8(v_toEnvExtension_3805_, sizeof(void*)*6);
lean_inc(v_n_3781_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_n_3781_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3808_);
v___x_3810_ = v___x_3802_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_index_3794_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_sourceString_3795_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_imports_3796_);
lean_ctor_set(v_reuseFailAlloc_3816_, 4, v_currNamespace_3797_);
lean_ctor_set(v_reuseFailAlloc_3816_, 5, v_openDecls_3798_);
lean_ctor_set(v_reuseFailAlloc_3816_, 6, v_options_3799_);
lean_ctor_set(v_reuseFailAlloc_3816_, 7, v_check_3800_);
v___x_3810_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___f_3811_; lean_object* v___x_3812_; 
v___f_3811_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoDocStringCore___at___00Lean_addVersoDocString_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_3811_, 0, v___x_3804_);
lean_closure_set(v___f_3811_, 1, v___x_3810_);
v___x_3812_ = lean_box(0);
if (v_logWrites_3807_ == 0)
{
lean_object* v___x_3813_; 
lean_inc_ref(v_toEnvExtension_3805_);
v___x_3813_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3805_, v_b_3786_, v___f_3811_, v_asyncMode_3806_, v___x_3812_, v___x_3782_);
v___y_3788_ = v___x_3813_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_inc_ref_n(v_toEnvExtension_3805_, 2);
v___x_3814_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3805_, v_b_3786_);
lean_dec_ref(v_b_3786_);
v___x_3815_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3805_, v___x_3814_, v___f_3811_, v_asyncMode_3806_, v___x_3812_, v___x_3782_);
v___y_3788_ = v___x_3815_;
goto v___jp_3787_;
}
}
}
}
else
{
lean_dec(v_n_3781_);
return v_b_3786_;
}
v___jp_3787_:
{
size_t v___x_3789_; size_t v___x_3790_; 
v___x_3789_ = ((size_t)1ULL);
v___x_3790_ = lean_usize_add(v_i_3784_, v___x_3789_);
v_i_3784_ = v___x_3790_;
v_b_3786_ = v___y_3788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1___boxed(lean_object* v_n_3819_, lean_object* v___x_3820_, lean_object* v_as_3821_, lean_object* v_i_3822_, lean_object* v_stop_3823_, lean_object* v_b_3824_){
_start:
{
uint8_t v___x_1351__boxed_3825_; size_t v_i_boxed_3826_; size_t v_stop_boxed_3827_; lean_object* v_res_3828_; 
v___x_1351__boxed_3825_ = lean_unbox(v___x_3820_);
v_i_boxed_3826_ = lean_unbox_usize(v_i_3822_);
lean_dec(v_i_3822_);
v_stop_boxed_3827_ = lean_unbox_usize(v_stop_3823_);
lean_dec(v_stop_3823_);
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_n_3819_, v___x_1351__boxed_3825_, v_as_3821_, v_i_boxed_3826_, v_stop_boxed_3827_, v_b_3824_);
lean_dec_ref(v_as_3821_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(lean_object* v_docs_3829_, lean_object* v_deferred_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; lean_object* v_env_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v___x_3838_ = lean_st_ref_get(v___y_3836_);
v_env_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc_ref(v_env_3839_);
lean_dec(v___x_3838_);
v___x_3840_ = l_Lean_getMainModuleDoc(v_env_3839_);
v___x_3841_ = l_Lean_PersistentArray_isEmpty___redArg(v___x_3840_);
lean_dec_ref(v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v_docs_3829_);
v___x_3842_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__3___closed__1);
v___x_3843_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3842_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v_env_3845_; lean_object* v___x_3846_; lean_object* v_size_3847_; lean_object* v___x_3848_; lean_object* v_env_3849_; lean_object* v___x_3850_; 
v___x_3844_ = lean_st_ref_get(v___y_3836_);
v_env_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc_ref(v_env_3845_);
lean_dec(v___x_3844_);
v___x_3846_ = l_Lean_getMainVersoModuleDocs(v_env_3845_);
v_size_3847_ = lean_ctor_get(v___x_3846_, 2);
lean_inc(v_size_3847_);
lean_dec_ref(v___x_3846_);
v___x_3848_ = lean_st_ref_get(v___y_3836_);
v_env_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc_ref(v_env_3849_);
lean_dec(v___x_3848_);
v___x_3850_ = l_Lean_addVersoModuleDocSnippet(v_env_3849_, v_docs_3829_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_dec(v_size_3847_);
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3852_ = lean_obj_once(&l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1, &l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1_once, _init_l_Lean_addVersoModDocStringCore___redArg___lam__0___closed__1);
v___x_3853_ = l_Lean_stringToMessageData(v_a_3851_);
v___x_3854_ = l_Lean_indentD(v___x_3853_);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3852_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = l_Lean_throwError___at___00Lean_addVersoDocString_spec__1___redArg(v___x_3855_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3856_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v_a_3857_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3850_, 1);
v___x_3858_ = lean_unsigned_to_nat(0u);
v___x_3859_ = lean_array_get_size(v_deferred_3830_);
v___x_3860_ = lean_nat_dec_lt(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v_size_3847_);
v___x_3861_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_a_3857_, v___y_3834_, v___y_3836_);
return v___x_3861_;
}
else
{
size_t v___x_3862_; size_t v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = lean_usize_of_nat(v___x_3859_);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__1(v_size_3847_, v___x_3841_, v_deferred_3830_, v___x_3862_, v___x_3863_, v_a_3857_);
v___x_3865_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v___x_3864_, v___y_3834_, v___y_3836_);
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0___boxed(lean_object* v_docs_3866_, lean_object* v_deferred_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_docs_3866_, v_deferred_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v_deferred_3867_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString(lean_object* v_range_3876_, lean_object* v_doc_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_versoModDocString(v_range_3876_, v_doc_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v___x_3889_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v_fst_3887_ = lean_ctor_get(v_a_3886_, 0);
lean_inc(v_fst_3887_);
v_snd_3888_ = lean_ctor_get(v_a_3886_, 1);
lean_inc(v_snd_3888_);
lean_dec(v_a_3886_);
v___x_3889_ = l_Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0(v_fst_3887_, v_snd_3888_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
lean_dec(v_snd_3888_);
return v___x_3889_;
}
else
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3897_; 
v_a_3890_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3892_ = v___x_3885_;
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3885_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3897_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3895_; 
if (v_isShared_3893_ == 0)
{
v___x_3895_ = v___x_3892_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3890_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addVersoModDocString___boxed(lean_object* v_range_3898_, lean_object* v_doc_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
lean_object* v_res_3907_; 
v_res_3907_ = l_Lean_addVersoModDocString(v_range_3898_, v_doc_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_doc_3899_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(lean_object* v_env_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___redArg(v_env_3908_, v___y_3912_, v___y_3914_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0___boxed(lean_object* v_env_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_setEnv___at___00Lean_addVersoModDocStringCore___at___00Lean_addVersoModDocString_spec__0_spec__0(v_env_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
return v_res_3925_;
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
